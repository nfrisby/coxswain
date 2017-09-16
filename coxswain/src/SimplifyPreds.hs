{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

-- | This module implements row unification and simplifies @Lacks@
-- constraints. It does so purely, separated from the
-- solution/generation/mutation of actual constraints.

module SimplifyPreds (
  Result(..),
  Result1(..),
  Step(..),
  simplifyPreds,
  ) where

import Data.Word (Word16)

import Articulation (Articulation(..))
import Col
import E
import GHCAPI
import Lacks
import LowLevel
import NormalForms
import Reduce
import Simplify

import qualified Outputable as D

-- | The next simplification, along with its required
-- unifications and articulations.
data Step a =
  MkStep ![(Type,Type)] ![Articulation] !a !(Maybe (Pred_ a))
  -- ^ @Nothing@ if a given is now fully consumed or a wanted is now
  -- fully proved.

-- | Result of simplifying a 'Pred'.
--
data NewStep a =
    NeedVar !TcTyVar !(TcTyVar -> NewStep a)
    -- ^ Request a fresh type variable.
  |
    NewStep !(Step a)
  | Message D.SDoc (NewStep a)

data Result1 = forall a. Step !Ct !(Pred_ a) !(Step a)

-- | The result of simplifying a set of 'Pred's.
data Result =
    Contra !Ct
  |
    Results [Result1]

simplifyPreds :: E -> [(Ct,Pred)] -> TcPluginM Result
simplifyPreds e = go []
  where
  feed :: NewStep a -> TcPluginM (Step a)
  feed = \case
    NewStep step -> return step
    NeedVar tv cont -> thawTyVar tv >>= feed . cont
    Message doc step -> do dumpTrace_ e "message" doc; feed step

  go acc = \case
    [] -> return (Results acc)
    (ct,MkPred ev pred_):ctps -> case simplify_Pred e ev pred_ of
      Contradiction -> return (Contra ct)
      Progress x -> do
        step0 <- feed x
        let MkStep uni0 art ev' pred' = step0
        let uni1 = filter (not . uncurry eqType) uni0
        let step = MkStep uni1 art ev' pred'
        let acc' = Step ct pred_ step:acc
        -- Hand new equalities back to GHC as soon as possible.
        if null uni0 && null art then go acc' ctps else return (Results acc')
      Yield -> go acc ctps

-----

simplify_Pred :: E -> a -> Pred_ a -> Simplification (NewStep a)
simplify_Pred e ev p = case asp of
  Yield ->
    maybe Yield (Progress . NewStep . MkStep [] [] ev . Just) (try_reduce e p)
  _ -> asp
  where
  asp = actually_simplify_Pred e ev p

actually_simplify_Pred :: E -> a -> Pred_ a -> Simplification (NewStep a)
actually_simplify_Pred e ev = \case
  ColEq lhs rhs -> simplify_ColEq e lhs rhs
  Lacks kl kt p l -> simplify_Lacks kl kt p l ev
  RowEq lhs rhs -> simplify_RowEq e lhs rhs

-----

-- TODO Is this superceded by the type family dependency?
simplify_ColEq :: E -> Col -> Col -> Simplification (NewStep ())
simplify_ColEq e lhs rhs = case (lhs,rhs) of
  -- Rule:
  --  alpha ~ c   -->   TRUE [c / alpha]
  (VarCol{},_) -> progress [(frCol e lhs,frCol e rhs)]
  (_,VarCol{}) -> progress [(frCol e lhs,frCol e rhs)]

  -- Rule:
  --   l1 .= t1 ~ l2 .= t2   -->   l1 ~ l2, t1 ~ t2   (Injectivity)
  (Col l1 t1,Col l2 t2) -> progress [(l1,l2),(t1,t2)]

  _ -> Yield
  where
  progress unis = Progress $ NewStep $ MkStep unis [] () Nothing

-----

simplify_Lacks :: Kind -> Kind -> Row -> Type -> Word16 -> Simplification (NewStep Word16)
simplify_Lacks kl kt (Exts root kcols0) l n0 =
  go False id n0 kcols0
  where
  go !progress acc !n = \case
    kcol:kcols -> case shiftLacks l kcol of
      Contradiction -> Contradiction
      -- Rule:
      --   Lacks (p .& l') l    -->   Lacks p l   [with appropriately adjusted evidence]
      Progress delta -> go True acc (n + delta) kcols
      Yield -> go progress (acc . (kcol:)) n kcols
    -- Rule:
    --   Lacks Row0 l   -->   TRUE
    [] -> case root of
      EmptyRow{} -> Progress $ NewStep $ MkStep [] [] n $ Nothing
      _
        | progress -> Progress $ NewStep $ MkStep [] [] n $ Just $ Lacks kl kt (Exts root (acc [])) l
        | otherwise -> Yield

-----

-- Note that we try articulation last, hoping other simplifications
-- will discharge the constraint by revealing enough reflexivity; we
-- prefer to not generate unnecessary articulate variables.
simplify_RowEq :: E -> Row -> Row -> Simplification (NewStep ())
simplify_RowEq e lhs@(Exts rootL kcolsL) rhs@(Exts rootR kcolsR)
  -- Rule:
  --   p ~ p   -->   TRUE

  | reflexive
  = Progress $ Message (D.text "refl") $ NewStep $ MkStep both [] () Nothing

  -- Rule:
  --   alpha ~ p   -->   TRUE [p / alpha]

  | null kcolsL, VarRow{} <- rootL
  = Progress $ Message (D.text "varL") $ NewStep $ MkStep [(frRow e lhs,frRow e rhs)] [] () Nothing
  | null kcolsR, VarRow{} <- rootR
  = Progress $ Message (D.text "varR") $ NewStep $ MkStep [(frRow e lhs,frRow e rhs)] [] () Nothing

  -- Rule:
  --   p .& c1 ~ p .& c2   -->   c1 ~ c2

  | Just colEq <- colInjectivity
  = Progress $ Message (D.text "colEq") $ NewStep $ MkStep both [] () (Just colEq)

  -- Rules:
  --   p .& c ~ q .& c   -->   p ~ q
  --   p .& l .= t ~ q .& l .= s   -->   p ~ q [unify s t]

  -- dropping shared columns
  | dropping
  = Progress $ Message (D.text "dropping " D.<> dmore) $ NewStep $ MkStep both [] () $ if reflexive then Nothing else Just (pred' rootL rootR)

  -- Rule:
  --   p .& col ~ 0   -->   FALSE

  | EmptyRow{} <- rootL, articulateL
  = Contradiction

  | EmptyRow{} <- rootR, articulateR
  = Contradiction

  -- Rule:
  --   p .& l .= t ~ q .& m .= s   -->   p ~ q' .& m .= s  [q' .& l .= t / q]

  -- articulating both sides
  | articulateL, VarRow vL <- rootL
  , articulateR, VarRow vR <- rootR
  = Progress $ Message (D.text "art2") $ NeedVar vL $ \vL' -> NeedVar vR $ \vR' ->
      NewStep $ MkStep both
        [MkArticulation vL vL' onlyR,MkArticulation vR vR' onlyL]
        ()
        (Just $ pred' (VarRow vL') (VarRow vR'))

  -- articulating left side
  | articulateL, VarRow vL <- rootL
  = Progress $ Message (D.text "artL") $ NeedVar vL $ \vL' ->
      NewStep $ MkStep both
        [MkArticulation vL vL' onlyR]
        ()
        (Just $ pred' (VarRow vL') rootR)

  -- articulating right side
  | articulateR, VarRow vR <- rootR
  = Progress $ Message (D.text "artR") $ NeedVar vR $ \vR' ->
      NewStep $ MkStep both
        [MkArticulation vR vR' onlyL]
        ()
        (Just $ pred' rootL (VarRow vR'))

  -- no progress can be made
  | otherwise = Yield

  where
  thd (_,_,x) = x
  dmore = D.ppr (map (frCol e . thd) kcolsL,map (frCol e . thd) kcolsL',map (frCol e . thd) kcolsR,map (frCol e . thd) kcolsR')

  colInjectivity = case (kcolsL',kcolsR') of
    ([(_,_,c1)],[(_,_,c2)])
      | eqRowRoot rootL rootR
      -> Just (ColEq c1 c2)
    _ -> Nothing

  reflexive = Exts rootL kcolsL' `eqRow` Exts rootR kcolsR'

  pred' rootL' rootR' = Exts rootL' kcolsL' `RowEq` Exts rootR' kcolsR'

  kcolsL' = [ kcol | (kcol,presence) <- judgeL, shouldRetainColumn articulatableR presence ]
  kcolsR' = [ kcol | (kcol,presence) <- judgeR, shouldRetainColumn articulatableL presence ]

  -- We can only articulate variables.
  articulatableL = case rootL of VarRow{} -> True; _ -> False
  articulatableR = case rootR of VarRow{} -> True; _ -> False

  shouldRetainColumn otherSideArticulatable = \case
    Absent -> dropping || not otherSideArticulatable
    Present{} -> False
    UnknownPresence -> True

  -- Articulate a side if it's definitely missing columns from the
  -- other side
  articulateL = not (null onlyR)
  articulateR = not (null onlyL)

  -- Remove columns that are on both sides (their types get unified).
  dropping = not (null both)

  -- Columns manifestly on both sides.
  both = [ uni | (_,Present (Just uni)) <- judgeL ]

  -- Columns manifestly on only one side.
  onlyL = [ kcol | (kcol,Absent) <- judgeL ]
  onlyR = [ kcol | (kcol,Absent) <- judgeR ]

  -- Are these columns present on the other side?
  judgeL = [ (kcol,lookupCol kcol kcolsR) | kcol <- kcolsL ]
  judgeR = [ (kcol,lookupCol kcol kcolsL) | kcol <- kcolsR ]
