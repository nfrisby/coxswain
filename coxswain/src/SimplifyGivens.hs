{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module SimplifyGivens (renSubst,simplifyGivens,slurpRen) where

import Control.Monad (foldM,forM)
import Data.Either (partitionEithers)
import Data.Monoid ((<>))
import Data.List (partition)
import Data.Word (Word16)

import Articulation
import E
import GHCAPI
import KnownNat16
import LowLevel
import NormalForms
import Reduce (try_reduce)
import Simplify
import SimplifyPreds
import WorkingCt
import ZonkGivens

-----

splitCts :: E -> [(Ct,Ct)] -> ([(Ct,PredType)],[(Ct,Pred)])
splitCts e = go [] []
  where
  go others preds = \case
    [] -> (others,preds)
    (ct,ct1):ctzcts -> case toPred e pt of
      Just pred0 | interesting pred0 -> go others ((ct,pred0):preds) ctzcts
      _ -> go ((ct,pt):others) preds ctzcts
      where
      pt = ctPred ct1
      interesting :: Pred -> Bool
      interesting = \case
        MkPred _ (RowEq (Exts _ l) (Exts _ r)) -> isCTyEqCan ct && not (null l) && not (null r)
          -- When False, the RowEq merely unifies a var; GHC will
          -- handle it.
        MkPred _ ColEq{} -> False
          -- I'm pretty sure the injectivity annotation on .= is
          -- enough, so disabling this for now.
        MkPred _ Lacks{} -> True

-----

renSubst :: InScopeSet -> [(a,(TyVar,Type))] -> TCvSubst
renSubst in_scope = foldl snoc (mkEmptyTCvSubst in_scope)
  where
  snoc sigma (_,(v,t)) = extendTvSubstAndInScope sigma v t

slurpRen :: E -> (a -> Ct) -> [a] -> ([(a,TyVar)],[(a,(TyVar,Type))],[a])
slurpRen e getCt = go [] [] []
  where
  go refl ren other = \case
    [] -> (refl,ren,other)
    a:as -> if

      | CDictCan{cc_class=c,cc_tyargs=[_,tv1,t2]} <- getCt a
      , c == renClass e
      , Just v1 <- getTyVar_maybe tv1
      -> case getTyVar_maybe t2 of
        Just v2 | v1 == v2 -> go ((a,v1):refl) ren other as
        _ -> go refl ((a,(v1,t2)):ren) other as

      | otherwise -> go refl ren (a:other) as

-----

simplifyGivens :: E -> [Ct] -> TcPluginM TcPluginResult
simplifyGivens e = working G activate simplifyGivens2 mb_deactivate e
  where
  activate = if cloThaw e then thawGivens else \_ _ -> return mempty
  mb_deactivate = if cloRefreeze e then Just refreezeGivens else Nothing

refreezeGivens :: E -> [Ct] -> TcPluginM SolvedNew
refreezeGivens e givens0 = let givens1 = zonkGivens givens0 in case slurpRen e snd givens1 of
  (_,_,[]) -> return mempty
  (_,rens,_) -> do

    let allVars = unionVarSets $ map (tyCoVarsOfType . ctPred) givens0
    let in_scope = mkInScopeSet allVars

    -- We partition the @$coxswainTau@ variables into three
    -- categories.
    --
    -- 1) Those occurring as the second argument of a @Ren@ constraint
    -- (i.e. manifestly equal to a genuine skolem, one actually bound
    -- by an implication constraint).
    --
    -- 2) Those occurring at the root of the second argument of a
    -- @Ren@ constraint (i.e. manifestly equal to some row restriction
    -- of a genuine skolem).
    --
    -- 3) All others.
    --
    -- The goal is to build a substitution that undoes the renaming
    -- that thawGivens introduced. Category 1 vars should be renamed
    -- back to a genuine skolem. Category 2 vars should be renamed to
    -- a fresh skolem. Category 3 vars should only occur in CTyEqCan
    -- constraints relating them to some other variable; these
    -- constraints should be discarded --- essentially, they were
    -- superceded by Category 2 variables.
    let
      (eqVars,restrictionVars) =
        partitionEithers $ map (\(_uniq,p) -> p) $ nonDetUFMToList $ foldl snoc emptyUFM rens
        where
        -- TODO Do collisions at the same summand matter? (E.G. resolve by tcLevel?)
        combo x@Left{} _ = x
        combo _ x = x
        snoc acc (_,(v1,t2)) = case toRow e t2 of
          Exts (VarRow v2) kcols
            | fsLit "$coxswainTau" == occNameFS (nameOccName (varName v2))
            -> addToUFM_C combo acc v2 (if null kcols then Left (v1,v2) else Right v2)
          _ -> acc
    let deadVars =
          filterVarSet ((== fsLit "$coxswainTau") . occNameFS . nameOccName . varName) otherVars
          where
          cat1and2 = concatMap (\(v1,v2) -> [v1,v2]) eqVars ++ restrictionVars
          otherVars = allRowVars `minusUniqSet` mkUniqSet cat1and2
          allRowVars = filterVarSet (isRowVar e) allVars
    _ <- dumpTrace e "eq vars" eqVars
    _ <- dumpTrace e "restriction vars" restrictionVars
    _ <- dumpTrace e "dead vars" (nonDetEltsUniqSet deadVars)
    (sigmaDom,_fresh,sigma) <- let
      snoc0 (sigmaDom,fresh,sigma) (v1,v2) = (v2:sigmaDom,fresh,extendTvSubstAndInScope sigma v2 (mkTyVarTy v1))
      snoc1 (sigmaDom,fresh,sigma) v2 = do
        v3 <- refreezeTyVar v2
        return (v2:sigmaDom,v3:fresh,extendTvSubstAndInScope sigma v2 (mkTyVarTy v3))
      in foldM snoc1 (foldl snoc0 ([],[],mkEmptyTCvSubst in_scope) eqVars) restrictionVars

    -- Apply the substitution to all constraints.
    fmap mconcat $ forM givens1 $ \(ct0,ct1) ->
      let noDead = isEmptyUniqSet $ tyCoVarsOfType (ctPred ct1) `intersectUniqSets` deadVars
      in
      if noDead
      then
        substGivenCt sigmaDom sigma (ct0,ct1) >>= return . \case
          Left sigmaFsk -> MkSolvedNew (if sigmaFsk then [(ctEvTerm (ctEvidence ct0),ct0)] else []) []
          Right ct2 -> MkSolvedNew [(ctEvTerm (ctEvidence ct0),ct0)] [ct2]
      else if (isCTyEqCan ct0 && cc_tyvar ct0 `elementOfUniqSet` deadVars) || isCFunEqCan ct0
        then return $ MkSolvedNew [(ctEvTerm (ctEvidence ct0),ct0)] []
        else dumpFlush e >> panic "Coxswain panic: at least one Dead variable occurs in a non-CTyEqCan" (ppr ct0)

-----

isRowVar :: E -> TyVar -> Bool
isRowVar e v = case splitTyConApp_maybe (tyVarKind v) of
  Just (hed,[_kl,_kt]) -> rowTC e == hed
  _ -> False

thawGivens :: E -> [Ct] -> TcPluginM SolvedNew
thawGivens e givens0 = do
  let allVars = unionVarSets $ map (tyCoVarsOfType . ctPred) givens0
  let in_scope = mkInScopeSet allVars

  -- A given @Ren v v@ means that we did not learn what the variable
  -- @v@ was from the givens of an enclosing implication. It should be
  -- rethawed, so that we might learn about it now.
  --
  -- A given @Ren v t@ means that we learned the variable @v@ was @t@
  -- from the givens of an enclosing implication. This @t / v@
  -- substitution should be applied to all the givens of this
  -- implication.
  --
  -- The rest of the row variables are either flattening skolems,
  -- fresh skolems that we generated when simplifying enclosing
  -- implications' givens (they'll be occ-named @$coxswainSko@), or
  -- genuine skolems newly bound by this implication
  -- constraint. Flatten skolems should be left alone. Skolems we
  -- generated should be rethawed but don't need a @Ren@
  -- constraint. New skolems should be thawed with a @Ren@ constraint.
  --
  -- We apply the new substitution to the RHSs of existing Ren
  -- constraints, and to all of the remaining constraints except
  -- flattening skolem definitions.
  let (refls,rens0,givens1) = slurpRen e snd (zonkGivens givens0)

  let oldVars = map snd refls ++ map (fst . snd) rens0
  let (renskos,newVars) =
        partition ((== fsLit "$coxswainSko") . occNameFS . nameOccName . varName) otherVars
        where
        otherVars = nonDetEltsUniqSet $ allRowVars `minusUniqSet` mkUniqSet oldVars
        relevant v = isRowVar e v && not (isFlattenTyVar v)
        allRowVars = filterVarSet relevant allVars

  rethawRen <- forM (map snd refls ++ renskos) $ \v -> (,) v <$> thawTyVar v
  thawRen <- forM newVars $ \v -> (,) v <$> thawTyVar v
  let sigma =
        -- Note: composeTCvSubst applies its first argument to the
        -- RHSs of its second argument.
        sigma1 `composeTCvSubst` sigma0
        where
        sigma0 = renSubst in_scope rens0
        sigma1 = foldl snoc1 (mkEmptyTCvSubst in_scope) (rethawRen ++ thawRen)
        snoc1 acc (v1,v2) = extendTvSubstAndInScope acc v1 (mkTyVarTy v2)
  let sigmaDom = map snd refls ++ renskos ++ newVars ++ map (fst . snd) rens0
  _ <- dumpTrace e "thaw subst" sigma

  -- Apply the substitution to all constraints.
  sn0 <- fmap mconcat $ forM givens1 $ \(ct0,ct1) -> substGivenCt sigmaDom sigma (ct0,ct1) >>= return . \case
    Left _ -> mempty
    Right ct2 -> MkSolvedNew [(ctEvTerm (ctEvidence ct0),ct0)] [ct2]

  -- Update given Rens, by applying the substitution to the second argument.
  sn1 <- fmap mconcat $ forM ([ (ctzct,(v,mkTyVarTy v)) | (ctzct,v) <- refls ] ++ rens0) $ \((ct0,_),(v,t)) -> do
    let ty = classTyCon (renClass e) `mkTyConApp` [tyVarKind v,mkTyVarTy v,substTy sigma t]
    let ev0 = ctEvTerm (ctEvidence ct0)
    (MkSolvedNew [(ev0,ct0)] . (:[])) <$> newGivenFrom ct0 ty

  -- Generate new Ren constraints.
  sn2 <- fmap (MkSolvedNew []) $ forM thawRen $ \(v1,v2) -> let
    ty = classTyCon (renClass e) `mkTyConApp` [tyVarKind v1,mkTyVarTy v1,mkTyVarTy v2]
    in newGivenFrom (head givens0) ty

  return $ sn0 <> sn1 <> sn2

simplifyGivens2 :: E -> [Ct] -> TcPluginM TcPluginResult
simplifyGivens2 e givens0 = do
  let
    relevant :: [(Ct,Pred)]
    (others,relevant) = splitCts e (zonkGivens givens0)

  snReduce <- reduceGiven e others   -- Note: simplifyPreds handles reductions in Preds.

  mapM (\(ct,pt) -> (,) ct <$> handsOff pt) relevant >>= simplifyPreds e >>= \case {
Contra contra -> return (TcPluginContradiction [contra]);
Results steps -> fmap (success . mappend snReduce . mconcat) $ forM steps $ \(Step ct pred0 (MkStep unis arts ev1 maybe_pred1)) -> do
  _ <- dumpTrace e "step" (frPred_ e pred0)
  sn0 <- fmap mconcat $ forM unis $ \(lhs,rhs) -> do
    ct1 <- newGivenEq ct lhs rhs
    return $ MkSolvedNew [] [ct1]
  sn1 <- fmap mconcat $ forM arts $ \(MkArticulation q q' exts) -> do
    let lhs = frRow e $ Exts (VarRow q') exts
    let rhs = mkTyVarTy q
    ct1 <- newGivenEq ct lhs rhs
    return $ MkSolvedNew [] [ct1]
  sn2 <- updateGivenCt e ct pred0 ev1 maybe_pred1
  return $ sn0 <> sn1 <> sn2
}

-----

reduceGiven :: E -> [(Ct,PredType)] -> TcPluginM SolvedNew
reduceGiven e = go [] []
  where
  go solved new = \case
    [] -> return $ MkSolvedNew solved new
    (ct,predType0):ctpts -> case try_reduce e predType0 of
      Nothing -> go solved new ctpts
      Just predType1 -> do
        let ev = ctEvTerm (ctEvidence ct)
        let solved1 = (ev,ct)
        new1 <- newGivenFrom ct predType1
        go (solved1:solved) (new1:new) ctpts

newGivenEq :: Ct -> Type -> Type -> TcPluginM Ct
newGivenEq ct lhs rhs = newGivenFrom ct (mkPrimEqPred lhs rhs)

newGivenFrom :: Ct -> Type -> TcPluginM Ct
newGivenFrom ct predType1 = mkNonCanonical <$> newGivenCtEvFrom ct predType1

newGivenCtEvFrom :: Ct -> Type -> TcPluginM CtEvidence
newGivenCtEvFrom ct predType1 = do
  let ctev = ctEvidence ct
  let predType0 = ctEvPred ctev
  let ev = ctEvTerm ctev
  newGiven (ctLoc ct) predType1 (coxFiatCast predType0 predType1 ev)

updateGivenCt :: E -> Ct -> Pred_ a -> a -> Maybe (Pred_ a) -> TcPluginM SolvedNew
updateGivenCt e ct pred0 ev1 maybe_pred1 = do
  let predType0 = frPred_ e pred0
  let evterm0 = ctEvTerm (ctEvidence ct)
  new <- case maybe_pred1 of
    Nothing -> return []
    Just pred1 -> do
      let predType1 = frPred_ e pred1
      let evterm1 = case pred1 of
            Lacks kl kt p l -> shiftGivenEvTerm e kl kt p l ev1 predType1 evterm0
            _ -> coxFiatCast predType0 predType1 evterm0
      (:[]) <$> mkNonCanonical <$> newGiven (ctLoc ct) predType1 evterm1
  return $ MkSolvedNew [(evterm0,ct)] new

shiftGivenEvTerm :: E -> Kind -> Kind -> Row -> Type -> Word16 -> Type -> EvTerm -> EvTerm
shiftGivenEvTerm e kl kt p l n predType1 ev0 =
  if 0 == n
  then coxFiatCast predType0 predType1 ev0
  else coxFiatCast middle predType1 $ EvDFunApp
    (minusLacksDFunId e)
    [kl,kt,frRow e p,l]
    [ev0,knownNat16EvTerm e n]
  where
  p' = frRow e p
  middle = classTyCon (minusLacksCls e) `mkTyConApp` [kt,kl,p',l]  -- necessary kt and kl swap
  predType0 = frPred_ e (Lacks kl kt p l)

-----

substGivenCt :: [TyVar] -> TCvSubst -> (Ct,Ct) -> TcPluginM (Either Bool Ct)
substGivenCt sigmaDom sigma (ct0,ct1) = do
  let ty1 = ctPred ct1
  let disjoint = isEmptyUniqSet $ tyCoVarsOfType ty1 `intersectUniqSets` mkUniqSet sigmaDom
  case ct0 of
    _ | disjoint -> return (Left False)
    CFunEqCan{} -> return (Left True)
    CDictCan{} -> do   -- Careful to preserve cc_pend_sc!
      let c = cc_class ct1
      let xis2 = map (substTy sigma) (cc_tyargs ct1)
      ctev2 <- newGivenCtEvFrom ct0 $ classTyCon c `mkTyConApp` xis2
      -- This often breaks the "xi flattened" invariant, but an
      -- immediately subsequent canonicalization pass fixes it
      -- up. (I.E. GHC is wise enough to not actually trust
      -- plugins...)
      return $ Right $ CDictCan{cc_ev = ctev2,cc_class = c,cc_tyargs = xis2,cc_pend_sc = cc_pend_sc ct0}
    _ -> Right <$> newGivenFrom ct0 (substTy sigma ty1)
