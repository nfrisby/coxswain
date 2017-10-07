{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module SimplifyWanteds (simplifyWanteds) where

import Control.Monad (forM)

import Articulation
import Data.Monoid ((<>))
import Data.Word (Word16)
import E
import GHCAPI
import KnownNat16
import LowLevel
import NormalForms
import Reduce (try_reduce)
import SimplifyGivens (renSubst,slurpRen)
import Simplify
import SimplifyPreds
import WorkingCt
import ZonkGivens

-----

splitCts :: E -> [Ct] -> ([(Ct,PredType)],[(Ct,Pred)])
splitCts e = go [] []
  where
  go others preds = \case
    [] -> (others,preds)
    ct:cts -> case toPred e pt of
      Just pred0 | interesting pred0 -> go others ((ct,pred0):preds) cts
      _ -> go ((ct,pt):others) preds cts
      where
      pt = ctEvPred (ctEvidence ct)
      interesting :: Pred -> Bool
      interesting = \case
        MkPred _ (RowEq (Exts _ l) (Exts _ r)) -> not (null l || null r)
        MkPred _ ColEq{} -> False
        MkPred _ Lacks{} -> True

-----

simplifyWanteds :: E -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
simplifyWanteds =
  \e gs ds ws -> working W activate simplifyWanteds2 (Just replaceRestrictionSkolems) e (gs,ds,ws)
  where
  activate e (gs,ds,ws)  = do
    drv <- activateGivens gs
    hypo <- activateRens e gs (ds ++ ws)
    return $ MkSolvedNew [] drv <> hypo

-- Givens equalities can't interact with Wanteds, so mirror them down
-- to Deriveds.
activateGivens :: [Ct] -> TcPluginM [Ct]
activateGivens givens = forM (filter isCTyEqCan givens) $ \ct -> do
  mkNonCanonical <$> newDerived (ctLoc ct) (ctEvPred (ctEvidence ct))

-- Apply the substitution recorded in the given Ren constraints.
activateRens :: E -> [Ct] -> [Ct] -> TcPluginM SolvedNew
activateRens e givens wanteds0 = do
  let allVars = unionVarSets $ map (tyCoVarsOfType . ctPred) (givens ++ wanteds0)
  let in_scope = mkInScopeSet allVars
  let (_,rens,_) = slurpRen e snd (zonkGivens givens)
  let sigmaDom = [ v | (_,(v,_)) <- rens ]
  let sigma = renSubst in_scope rens
  if null rens
    then return mempty
    else do
      _ <- dumpTrace e "rethaw subst" sigma
      fmap mconcat $ forM wanteds0 $ \ct0 -> substWantedCt sigmaDom sigma ct0 >>= return . \case
        Nothing -> mempty
        Just (ev0,ct1) -> MkSolvedNew [(ev0,ct0)] [ct1]

simplifyWanteds2 :: E -> ([Ct],[Ct],[Ct]) -> TcPluginM TcPluginResult
simplifyWanteds2 e (_,_,wanteds) = do
  let
    relevant :: [(Ct,Pred)]
    (others,relevant) = splitCts e wanteds

  snReduce <- reduceWanted e others   -- Note: simplifyPreds handles reductions in Preds.

  mapM (\(ct,pt) -> (,) ct <$> handsOff pt) relevant >>= simplifyPreds e >>= \case {
Contra contra -> return (TcPluginContradiction [contra]);
Results steps -> fmap (success . mappend snReduce . mconcat) $ forM steps $ \(Step ct pred0 (MkStep unis arts ev1 maybe_pred1)) -> do
  _ <- dumpTrace e "step" (frPred_ e pred0,frPred_ e <$> maybe_pred1)
  sn0 <- fmap mconcat $ forM unis $ \(lhs,rhs) -> do
    ct1 <- newWantedEq ct lhs rhs
    return $ MkSolvedNew [] [ct1]
  sn1 <- fmap mconcat $ forM arts $ \(MkArticulation q q' exts) -> do
    let lhs = frRow e $ Exts (VarRow q') exts
    let rhs = mkTyVarTy q
    ct1 <- newWantedEq ct lhs rhs
    return $ MkSolvedNew [] [ct1]
  sn2 <- updateWantedCt e ct pred0 ev1 maybe_pred1
  return $ sn0 <> sn1 <> sn2
}

-- | This pass is only necessary for the sake of error messages: GHC
-- panics when trying to render one of our restriction skolems because
-- isn't actually bound by the implication constraint it claims to be
-- bound by.
--
-- Note that: error messages arise from 1) having given constraints
-- that incur restriction skolems and 2) having *unsolved* wanteds
-- under those givens. If your given constraints are "simple" or you
-- don't have error messages, then this pass will be unnecessary.
--
-- TODO: Contradictions also need this, but I haven't done that yet
-- because it'll require me to rewrite some of the "WorkingCt"
-- infrastructure.
replaceRestrictionSkolems :: E -> ([Ct],[Ct],[Ct]) -> TcPluginM SolvedNew
replaceRestrictionSkolems e (gs0,_,ws) = let gs1 = zonkGivens gs0 in case slurpRen e snd gs1 of
  (_,_,[]) -> return mempty
  (_,rens,_) -> do

    let allVars = unionVarSets $ map (tyCoVarsOfType . ctPred) (gs0 ++ ws)
    let in_scope = mkInScopeSet allVars

    -- This collects all of the restriction skolems (see comment in
    -- refreezeGivens), associating each with one of the smallest
    -- restrictions that it's equal to.
    let
      restrictionVars :: [(TcTyVar,TcTyVar,(Kind,Kind,Col),[(Kind,Kind,Col)])]
      restrictionVars = map (\(_uniq,p) -> p) $ nonDetUFMToList $ foldl snoc emptyUFM rens
        where
        combo l@(v2,_,_,kcols1) (_,v12,kcol02,kcols2)
          | length kcols2 < length kcols1 = (v2,v12,kcol02,kcols2)
          | otherwise = l
        snoc acc (_,(v1,t2)) = case toRow e t2 of
          Exts (VarRow v2) (kcol0:kcols)
            | fsLit "$coxswainSko" == occNameFS (nameOccName (varName v2))
            -> addToUFM_C combo acc v2 (v2,v1,kcol0,kcols)
          _ -> acc

    -- Create a substitution that renames all $coxswainTau variables
    -- to the @rho@ occ-name.
    let
      tauVars = nonDetEltsUniqSet $ unionVarSets $ map (filterVarSet keep . tyCoVarsOfType . ctPred) ws
        where
        keep = (== fsLit "$coxswainTau") . occNameFS . nameOccName . varName

      tauSigma = foldl snoc (mkEmptyTCvSubst in_scope) tauVars
        where
        snoc acc v = extendTvSubstAndInScope acc v $ mkTyVarTy $ setTyVarName v $ tidyNameOcc (varName v) (mkTyVarOccFS (fsLit "rho"))

    -- Create a substitution that replaces all skolm restrictions with
    -- their associated restriction.
    let
      mkColRow = \kcol0@(kl,kt,_) -> foldl snoc ((rowTC e `mkTyConApp` [kl,kt]) `snoc` kcol0)
        where
        snoc acc (kl,kt,Col l _) = extTC e `mkTyConApp` [kl,kt,acc,mkColTC e `mkTyConApp` [kl,kt,l,anyTyCon `mkTyConApp` [kt]]]
        snoc _ _ = panic "column variable in a restriction"
      mkRestriction v1 kcol0@(kl,kt,_) kcols = restrictionTC e `mkTyConApp` [kl,kt,mkTyVarTy v1,mkColRow kcol0 kcols]

      sigmaDom = [ v2 | (v2,_,_,_) <- restrictionVars ] ++ tauVars
      sigma = foldl snoc tauSigma restrictionVars
        where
        snoc acc (v2,v1,kcol0,kcols) = extendTvSubstAndInScope acc v2 (mkRestriction v1 kcol0 kcols)

    -- Apply the substitution to all Wanted constraints.
    fmap mconcat $ forM ws $ \ct0 -> substWantedCt sigmaDom sigma ct0 >>= return . \case
      Nothing -> mempty
      Just (ev0,ct1) -> MkSolvedNew [(ev0,ct0)] [ct1]

-----

reduceWanted :: E -> [(Ct,PredType)] -> TcPluginM SolvedNew
reduceWanted e = go [] []
  where
  go solved new = \case
    [] -> return $ MkSolvedNew solved new
    (ct,predType0):ctpts -> case try_reduce e predType0 of
      Nothing -> go solved new ctpts
      Just predType1 -> do
        ctev1 <- newWanted (ctLoc ct) predType1
        let ev = ctEvTerm ctev1
        let solved1 = (coxFiatCast predType1 predType0 ev,ct)
        go (solved1:solved) (mkNonCanonical ctev1:new) ctpts

newWantedEq :: Ct -> Type -> Type -> TcPluginM Ct
newWantedEq ct lhs rhs = mkNonCanonical <$> newWanted (ctLoc ct) (mkPrimEqPred lhs rhs)

updateWantedCt :: E -> Ct -> Pred_ a -> a -> Maybe (Pred_ a) -> TcPluginM SolvedNew
updateWantedCt e ct pred0 evi1 maybe_pred1 = case maybe_pred1 of
  Nothing -> case pred0 of
    ColEq lhs _ -> solveEq (frCol e lhs)
    Lacks kl kt p l -> return $ MkSolvedNew [(doneWantedEvTerm e kl kt p l evi1,ct)] []
    RowEq lhs _ -> solveEq (frRow e lhs)
    where
    solveEq :: Type -> TcPluginM SolvedNew
    solveEq lhs = do
      ct' <- newWantedEq ct lhs lhs
      let ev = coxFiatCast (ctPred ct') (ctPred ct) (ctEvTerm (ctEvidence ct'))
      return $ MkSolvedNew [(ev,ct)] [ct']
  Just pred1 -> do
    let predType0 = frPred_ e pred0
    let predType1 = frPred_ e pred1
    ctev1 <- newWanted (ctLoc ct) predType1
    let ev1 = ctEvTerm ctev1
    let ev = case pred1 of
          Lacks kl kt p l -> shiftWantedEvTerm e kl kt p l evi1 predType0 ev1
          _ -> coxFiatCast predType1 predType0 ev1
    return $ MkSolvedNew [(ev,ct)] [mkNonCanonical ctev1]

shiftWantedEvTerm :: E -> Kind -> Kind -> Row -> Type -> Word16 -> Type -> EvTerm -> EvTerm
shiftWantedEvTerm e kl kt p l n predType0 ev1 =
  if 0 == n
  then coxFiatCast predType1 predType0 ev1
  else coxFiatCast middle predType0 $ EvDFunApp
    (plusLacksDFunId e)
    [kl,kt,p',l]
    [ev1,knownNat16EvTerm e n]
  where
  p' = frRow e p
  middle = classTyCon (plusLacksCls e) `mkTyConApp` [kt,kl,p',l]  -- necessary kt and kl swap
  predType1 = frPred_ e (Lacks kl kt p l)

doneWantedEvTerm :: E -> Kind -> Kind -> Row -> Type -> Word16 -> EvTerm
doneWantedEvTerm e kl kt p l n =
  coxFiatCast predType0 predType1 (knownNat16EvTerm e n)
  where
  predType0 = knownNat16Type e
  predType1 = frPred_ e (Lacks kl kt p l)

-----

substWantedCt :: [TyVar] -> TCvSubst -> Ct -> TcPluginM (Maybe (EvTerm,Ct))
substWantedCt sigmaDom sigma ct1 = do
  let ty1 = ctPred ct1
  let disjoint = isEmptyUniqSet $ tyCoVarsOfType ty1 `intersectUniqSets` mkUniqSet sigmaDom
  case ct1 of
    _ | disjoint -> return Nothing
    CFunEqCan{} -> return Nothing
    CDictCan{} -> do   -- Careful to preserve cc_pend_sc!
      let c = cc_class ct1
      let xis2 = map (substTy sigma) (cc_tyargs ct1)
      let ty2 = classTyCon c `mkTyConApp` xis2
      ctev2 <- newWanted (ctLoc ct1) ty2
      -- This often breaks the "xi flattened" invariant, but an
      -- immediately subsequent canonicalization pass fixes it
      -- up. (I.E. GHC is wise enough to not actually trust
      -- plugins...)
      let ev2 = ctEvTerm ctev2
      let ct2 = CDictCan{cc_ev = ctev2,cc_class = c,cc_tyargs = xis2,cc_pend_sc = cc_pend_sc ct1}
      return $ Just $ (coxFiatCast ty2 ty1 ev2,ct2)
    _ -> do
      let ty2 = substTy sigma ty1
      ctev2 <- newWanted (ctLoc ct1) ty2
      let ev2 = ctEvTerm ctev2
      let ct2 = mkNonCanonical ctev2
      return $ Just $ (coxFiatCast ty2 ty1 ev2,ct2)
