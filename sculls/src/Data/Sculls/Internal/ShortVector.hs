{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Sculls.Internal.ShortVector (
  SV(..),
  Short(..),
  ) where

import Data.Word (Word16)
import GHC.TypeLits (type (+),Nat)

import Data.Sculls.Internal.ShortVectorTH

-- | A short, homogenous, and strict tuple
data family SV (n :: Nat) :: * -> *
data instance SV 0 a = V0 deriving (Foldable,Functor,Show,Traversable)
newtype instance SV 1 a = V1 a deriving (Foldable,Functor,Show,Traversable)

$(concat <$> mapM dataTH [2..17])

instance Applicative (SV 0) where
  pure = const V0
  V0 <*> V0 = V0
instance Applicative (SV 1) where
  pure = V1
  V1 f <*> V1 a = V1 (f a)

type Fin (n :: Nat) = Word16

-- | Predicate for supported record sizes.
class (Applicative (SV n),Traversable (SV n)) => Short (n :: Nat) where
  select :: SV (n + 1) a -> Fin (n + 1) -> a
  lensSV :: Functor f => (a -> f a) -> SV (n + 1) a -> Fin (n + 1) -> f (SV (n + 1) a)
  extend :: SV n a -> a -> Fin (n + 1) -> SV (n + 1) a
  restrict :: SV (n + 1) a -> Fin (n + 1) -> (a,SV n a)
  indices :: SV n (Fin n)

instance Short 0 where
  {-# INLINE select #-}
  select (V1 a) _ = a
  {-# INLINE lensSV #-}
  lensSV f (V1 a) _ = V1 <$> f a
  {-# INLINE extend #-}
  extend V0 x _ = V1 x
  {-# INLINE restrict #-}
  restrict (V1 a) _ = (a,V0)
  {-# INLINE indices #-}
  indices = V0
instance Short 1 where
  {-# INLINE select #-}
  select (V2 a b) = \case
    1 -> b
    _ -> a
  {-# INLINE lensSV #-}
  lensSV f (V2 a b) = \case
    1 -> (\x -> V2 a x) <$> f b
    _ -> (\x -> V2 x b) <$> f a
  {-# INLINE extend #-}
  extend (V1 a) x = \case
    1 -> V2 a x
    _ -> V2 x a
  {-# INLINE restrict #-}
  restrict (V2 a b) = \case
    1 -> (b,V1 a)
    _ -> (a,V1 b)
  {-# INLINE indices #-}
  indices = V1 0

$(concat <$> mapM shortTH [2..16])
