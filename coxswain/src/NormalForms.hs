{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

-- | Each data type in this module partitions 'Type' into somes cases
-- of interest to the plugin's constraint simplifier.
--
-- For each data type, there is a pair of @to*@ and @fr*@ functions
-- witnessing an embedding or isomorphism from 'Type'.

module NormalForms (
  -- * Column types
  Col(..),
  eqCol,
  frCol,
  toCol,

  -- * Row types
  Row(..),
  RowRoot(..),
  eqRow,
  eqRowRoot,
  frRow,
  sizeRow,
  toRow,
  toRowAcc,

  -- * Predicates
  Pred(..),
  Pred_(..),
  frPred,
  frPred_,
  sizePred,
  toPred,

  -- * Traversals
  HandsOff(..),
  ) where

import Data.Word (Word16)

import E

import Class (classTyCon)
import TcPluginM (TcPluginM,isTouchableTcPluginM)
import Type (
  PredTree( ClassPred ),
  Kind,
  PredTree( EqPred ),
  PredType,
  EqRel( NomEq ),
  TyVar,
  Type,
  classifyPredType,
  eqType,
  getTyVar_maybe,
  mkPrimEqPred,
  mkTyConApp,
  mkTyVarTy,
  splitTyConApp_maybe,
  typeKind,
  )

-----

data Col =
    Col !Type !Type   -- ^ @l .= t@
  |
    VarCol !TyVar   -- ^ @alpha@
  |
    ElseCol !Type   -- ^ None of the other constructors

eqCol :: Col -> Col -> Bool
eqCol (Col l1 t1) (Col l2 t2) = eqType l1 l2 && eqType t1 t2
eqCol (VarCol v1) (VarCol v2) = v1 == v2
eqCol (ElseCol ty1) (ElseCol ty2) = eqType ty1 ty2
eqCol _ _ = False

toCol :: E -> Type -> Col
toCol e ty = if

  | Just (hed,[_,_,l,t]) <- splitTyConApp_maybe ty
  , hed == mkColTC e
  -> Col l t

  | Just v <- getTyVar_maybe ty -> VarCol v

  | otherwise -> ElseCol ty

frCol :: E -> Col -> Type
frCol e ty = case ty of
  Col l t -> mkColTC e `mkTyConApp` [typeKind l,typeKind t,l,t]
  VarCol v -> mkTyVarTy v
  ElseCol ty2 -> ty2

-----

data Row = Exts !RowRoot ![(Kind,Kind,Col)]
   -- ^ @p .& c1 .& c2 .& ... .& cN@. The outermost column is the
   -- first element in the list (i.e. it's "backwards" wrt to
   -- left-to-right, but it's equivalent wrt nesting).

data RowRoot =
    EmptyRow !Kind !Kind   -- ^ @Row0 :: Row kl kt@
  |
    VarRow !TyVar   -- ^ @alpha@
  |
    ElseRow !Type   -- ^ None of the other constructors

-- | @'toRow' e = 'toRowAcc' e id@.
toRow :: E -> Type -> Row
toRow e = toRowAcc e id

-- | The accumulator carries the columns of the extensions we're already
-- under.
toRowAcc :: E -> ([(Kind,Kind,Col)] -> [(Kind,Kind,Col)]) -> Type -> Row
toRowAcc e = go
  where
  exts p acc = Exts p (acc [])

  go acc ty = case splitTyConApp_maybe ty of
    Just (hed,[kl,kt]) | hed == emptyTC e -> EmptyRow kl kt `exts` acc
    Just (hed,[kl,kt,p,col]) | hed == extTC e -> go (acc . ((kl,kt,toCol e col):)) p
    _ | Just v <- getTyVar_maybe ty -> VarRow v `exts` acc
    _ -> ElseRow ty `exts` acc

frRow :: E -> Row -> Type
frRow e (Exts p0 kcols) = foldr cons nil kcols
  where
  nil = case p0 of
    EmptyRow kl kt -> emptyTC e `mkTyConApp` [kl,kt]
    VarRow v -> mkTyVarTy v
    ElseRow ty -> ty
  cons (kl,kt,col) p = extTC e `mkTyConApp` [kl,kt,p,frCol e col]

eqRow :: Row -> Row -> Bool
eqRow (Exts root1 kcols1) (Exts root2 kcols2) =
  eqRowRoot root1 root2 && go kcols1 kcols2
  where
  go [] [] = True
  go [] _ = False
  go _ [] = False
  go ((kl1,kt1,col1):ls) ((kl2,kt2,col2):rs) = eqType kl1 kl2 && eqType kt1 kt2 && eqCol col1 col2 && go ls rs

eqRowRoot :: RowRoot -> RowRoot -> Bool
eqRowRoot (EmptyRow kl1 kt1) (EmptyRow kl2 kt2) = eqType kl1 kl2 && eqType kt1 kt2
eqRowRoot (VarRow v1) (VarRow v2) = v1 == v2
eqRowRoot (ElseRow ty1) (ElseRow ty2) = eqType ty1 ty2
eqRowRoot _ _ = False

sizeRow :: Row -> Int
sizeRow (Exts _ kcols) = length kcols

-----

-- | A predicate indexed by the type of its evidence.
data Pred_ :: * -> * where
  -- | @lhs ~ rhs :: Col k@
  ColEq :: !Col -> !Col -> Pred_ ()
  -- | @kl kt p l n@ where the evidence for @Lacks kl kt p l@ is @n@
  -- less than that for the originating constraint.
  Lacks :: !Kind -> !Kind -> !Row -> !Type -> Pred_ Word16
  -- | @lhs ~ rhs :: Row kl kt@
  RowEq :: !Row -> !Row -> Pred_ ()

-- | A predicate and its evidence.
data Pred where
  MkPred :: evi -> Pred_ evi -> Pred

-- | Returns 'Just' for a predicate that we may be able to simplify
-- more than just reducing a type family application subterm somewhere
-- inside it.
toPred :: E -> PredType -> Maybe Pred
toPred e = (. classifyPredType) $ \case
  EqPred NomEq t1 t2

    | Just (hed,[_kl,_kt]) <- splitTyConApp_maybe (typeKind t1)
    , colTC e == hed
    -> Just $ MkPred () $ ColEq (toCol e t1) (toCol e t2)

    | Just (hed,[_kl,_kt]) <- splitTyConApp_maybe (typeKind t1)
    , rowTC e == hed
    -> Just $ MkPred () $ RowEq (toRow e t1) (toRow e t2)

  ClassPred c [kt,kl,p,l]   -- With -fprint-explicit-kinds, :i Coxswain.Lacks reveals its kind arguments are kt kl.
    | lacksCls e == c -> Just $ MkPred 0 $ Lacks kl kt (toRow e p) l

  _ -> Nothing

frPred_ :: E -> Pred_ a -> PredType
frPred_ e = \case
  ColEq lhs rhs -> mkPrimEqPred (frCol e lhs) (frCol e rhs)
  Lacks kl kt p l -> classTyCon (lacksCls e) `mkTyConApp` [kt,kl,frRow e p,l]
  RowEq lhs rhs -> mkPrimEqPred (frRow e lhs) (frRow e rhs)

frPred :: E -> Pred -> PredType
frPred e (MkPred _ pred_) = frPred_ e pred_

sizePred :: Pred -> Int
sizePred = \case
  MkPred _ ColEq{} -> 0
  MkPred _ (Lacks _ _ p _) -> sizeRow p
  MkPred _ (RowEq lhs rhs) -> sizeRow lhs + sizeRow rhs

-----

class HandsOff t where
  -- | Forget any untouchables are variables.
  handsOff :: t -> TcPluginM t

instance HandsOff Pred where
  handsOff (MkPred evi pred0) = MkPred evi <$> handsOff pred0

instance HandsOff (Pred_ a) where
  handsOff = \case
    RowEq lhs rhs -> RowEq <$> handsOff lhs <*> handsOff rhs
    Lacks kl kt p l -> Lacks kl kt <$> handsOff p <*> pure l
    ColEq lhs rhs -> ColEq <$> handsOff lhs <*> handsOff rhs

instance HandsOff Col where
  handsOff col = case col of
    VarCol v -> do
      b <- isTouchableTcPluginM v
      return $ if b then col else ElseCol (mkTyVarTy v)
    _ -> return col

instance HandsOff Row where
  handsOff (Exts root kcols) = flip Exts kcols <$> handsOff root

instance HandsOff RowRoot where
  handsOff root = case root of
    VarRow v -> do
      b <- isTouchableTcPluginM v
      return $ if b then root else ElseRow (mkTyVarTy v)
    _ -> return root
