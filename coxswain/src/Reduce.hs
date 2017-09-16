{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Reduce (Reduce,try_reduce) where

import E
import GHCAPI
import LowLevel (detCmpType)
import qualified MiniSYB as SYB
import NormalForms

import TcTypeNats (typeNatAddTyCon,typeNatSubTyCon)

import Control.Monad (foldM)
import Data.Monoid (Any(..))

class Reduce t where go :: E -> t -> (Any,t)

-- | Attempt to reduce occurrences of the @Normalize@ and @NumCols@
-- type families.
try_reduce :: Reduce t => E -> t -> Maybe t
try_reduce e t = if getAny hit then Just t' else Nothing
  where
  (hit,t') = go e t

instance Reduce Col where
  go e = \case
    Col l lt -> Col <$> go e l <*> go e lt
    o@VarCol{} -> pure o
    ElseCol t -> ElseCol <$> go e t

instance Reduce Row where
  go e (Exts root kcols0) =
    Exts <$> go e root <*> sequence kcols1
    where
    kcols1 = [ (,,) kl kt <$> go e col | (kl,kt,col) <- kcols0 ]

instance Reduce RowRoot where
  go e = \case
    o@EmptyRow{} -> pure o
    o@VarRow{} -> pure o
    ElseRow t -> ElseRow <$> go e t

instance Reduce (Pred_ a) where
  go e = \case
    ColEq lhs rhs -> ColEq <$> go e lhs <*> go e rhs
    Lacks kl kt p l -> Lacks kl kt <$> go e p <*> go e l
    RowEq lhs rhs -> RowEq <$> go e lhs <*> go e rhs

instance Reduce Type where
  go e = SYB.topDownM $ SYB.mkM $ \t -> if
    | Just (hed,[_,_,p]) <- splitTyConApp_maybe t
    , normTC e == hed
    , Exts (EmptyRow kl kt) kcols0 <- toRow e p
    , Just kcols1 <- sortColumns kcols0
    -> (Any True,mkNRow e kl kt kcols1)

    | Just (hed,[kl,kt,p]) <- splitTyConApp_maybe t
    , numColsTC e == hed
    , Exts root kcols0 <- toRow e p
    -> let n = toInteger (length kcols0) in case root of
      EmptyRow{} -> (Any True,mkNumLitTy n)
      _
        | n > 0 -> (,) (Any True) $
        typeNatAddTyCon `mkTyConApp`
          [numColsTC e `mkTyConApp` [kl,kt,frRow e (Exts root [])],mkNumLitTy n]
        | otherwise -> pure t

    | Just nat1 <- toNat1 t
    -> frNatNF (goNat1 (Right nat1))

    | otherwise -> pure t

mkNRow :: E -> Kind -> Kind -> [(Kind,Kind,Type,Type)] -> Type
mkNRow e kl0 kt0 = foldr
  (\(kl,kt,l,t) p -> nextTC e `mkTyConApp` [kl,kt,p,l,t])
  (nrowTC e `mkTyConApp` [kl0,kt0])

-- Sorts the columns, failing if any aren't concrete enough to fully
-- sort.
sortColumns :: [(Kind,Kind,Col)] -> Maybe [(Kind,Kind,Type,Type)]
sortColumns = foldM (flip insertSorted) []
  where
  insertSorted :: (Kind,Kind,Col) -> [(Kind,Kind,Type,Type)] -> Maybe [(Kind,Kind,Type,Type)]
  insertSorted (kl,kt,Col l lt) []
    = Just [(kl,kt,l,lt)]

  insertSorted kcol@(kl,kt,Col l lt) (mkcol@(_,_,m,_):kcols)
    | Just cmp <- detCmpType l m
    = case cmp of
      LT -> Just $ (kl,kt,l,lt) : mkcol : kcols
      EQ -> Nothing
      GT -> (mkcol:) <$> insertSorted kcol kcols

  insertSorted _ _
    = Nothing

-----

-- | The basic TypeNat shapes that are relevant to our normalization
-- scheme.
data Nat1 = Nat1Plus Type Type | Nat1Sub Type Type | Nat1Lit Integer

toNat1 :: Type -> Maybe Nat1
toNat1 = \t -> if
  | Just (hed,[n,m]) <- splitTyConApp_maybe t
  , typeNatAddTyCon == hed
  -> Just (Nat1Plus n m)

  | Just (hed,[n,m]) <- splitTyConApp_maybe t
  , typeNatSubTyCon == hed
  -> Just (Nat1Sub n m)

  | Just lit <- isNumLitTy t
  -> Just (Nat1Lit lit)

  | otherwise -> Nothing

frNat1 :: Nat1 -> Type
frNat1 = \case
  Nat1Plus l r -> typeNatAddTyCon `mkTyConApp` [l,r]
  Nat1Sub l r -> typeNatSubTyCon `mkTyConApp` [l,r]
  Nat1Lit lit
    | lit < 0 -> typeNatSubTyCon `mkTyConApp` [mkNumLitTy 0,mkNumLitTy (abs lit)]
    | otherwise -> mkNumLitTy lit

data NatNF = MkNatNF (Maybe Type) Integer Bool
  -- ^ A type (or not) plus a literal, with a flag if this is different than we started from.

frNatNF_ :: NatNF -> Type
frNatNF_ = snd . frNatNF

frNatNF :: NatNF -> (Any,Type)
frNatNF (MkNatNF mb_t lit hit) = (,) (Any hit) $ case mb_t of
  Nothing -> frNat1 (Nat1Lit lit)
  Just t -> case compare lit 0 of
    LT -> frNat1 (Nat1Sub t (mkNumLitTy (abs lit)))
    EQ -> t
    GT -> frNat1 (Nat1Plus t (mkNumLitTy lit))

-- Rules:
--  n + m   -->   o, where o = n + m
--  n + (t + m)   -->   t + o, where o = n + m
--  (t + n) + m   -->   t + o, where o = n + m
plusNatNF :: NatNF -> NatNF -> NatNF
plusNatNF (MkNatNF Nothing lit1 _) (MkNatNF mb_t lit2 _) = MkNatNF mb_t (lit1 + lit2) True
plusNatNF (MkNatNF mb_t lit1 _) (MkNatNF Nothing lit2 _) = MkNatNF mb_t (lit1 + lit2) True
plusNatNF l@(MkNatNF _ _ hit1) r@(MkNatNF _ _ hit2) = MkNatNF (Just t) 0 (hit1 || hit2)
  where
  t = frNat1 (Nat1Plus (frNatNF_ l) (frNatNF_ r))

-- Rule:
--  n - m   -->   o, where o = n - m
--  (t + n) - m   -->   t + o, where o = n - m
subNatNF :: NatNF -> NatNF -> NatNF
subNatNF (MkNatNF mb_t lit1 _) (MkNatNF Nothing lit2 _) = MkNatNF mb_t (lit1 - lit2) True
subNatNF l@(MkNatNF _ _ hit1) r@(MkNatNF _ _ hit2) = MkNatNF (Just t) 0 (hit1 || hit2)
  where
  t = frNat1 (Nat1Sub (frNatNF_ l) (frNatNF_ r))

-- | These are the non-literal base cases, where the syntax is already
-- equivalent to the normal form. If we don't special case these in
-- 'goNat1', then the myopic 'plusNatNF' and 'subNatNF' functions set
-- the flag even though they're just rebuilding the syntax that was
-- already there: infinite loop!
baseNat1 :: Nat1 -> Maybe NatNF
baseNat1 = \case
  Nat1Plus n m
    | Nothing <- toNat1 n
    , Just (Nat1Lit lit) <- toNat1 m
    -> Just $ MkNatNF (Just n) lit False

  Nat1Sub n m
    | Nothing <- toNat1 n
    , Just (Nat1Lit lit) <- toNat1 m
    -> Just $ MkNatNF (Just n) (negate lit) False

  _ -> Nothing

-- | A very simplistic constant folding pass, but it's sufficient for
-- the kinds of constraints that arise in the sculls package.
--
-- It tries to rewrite TypeNat terms to the form @a non-sum Nat + a
-- literal Nat@.
goNat1 :: Either Type Nat1 -> NatNF
goNat1 = \case
  Left t -> MkNatNF (Just t) 0 False
  Right nat1 -> case nat1 of
    _ | Just natNF <- baseNat1 nat1 -> natNF
    Nat1Plus n m -> plusNatNF (recur n) (recur m)
    Nat1Sub n m -> subNatNF (recur n) (recur m)
    Nat1Lit lit -> MkNatNF Nothing lit False
  where
  recur t = goNat1 $ maybe (Left t) Right $ toNat1 t
