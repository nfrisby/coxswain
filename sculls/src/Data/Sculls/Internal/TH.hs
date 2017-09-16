{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Utilities useful in the TH modules.

module Data.Sculls.Internal.TH (
  module Data.Sculls.Internal.TH,
  ) where

import Data.Char (isUpper)
import GHC.Generics ((:+:)(..))
import Language.Haskell.TH

noWhere :: [DecQ]
noWhere = []

class Namey t where nm :: String -> Q t

instance Namey Name where nm = return . mkName
instance Namey Exp where nm s = (if isUpper (head s) then conE else varE) (mkName s)
instance Namey Pat where nm s = (if isUpper (head s) then const (fail "Namey conP") else varP) (mkName s)
instance Namey Type where nm s = (if isUpper (head s) then conT else varT) (mkName s)

nV :: Namey t => Int -> Q t
nV k = nm ("V" ++ show k)

numT :: Int -> TypeQ
numT k = litT (numTyLit (toInteger k))

strT :: String -> TypeQ
strT s = litT (strTyLit s)

numP :: Int -> PatQ
numP k = litP (integerL (toInteger k))

numE :: Int -> ExpQ
numE k = litE (integerL (toInteger k))

names :: Int -> String -> [String]
names k s = [ s ++ show i | i <- [0..k-1] ]

vecP :: Int -> String -> PatQ
vecP k s = nV k >>= \n -> conP n $ map nm $ names k s

contexts :: [a] -> [([a] -> [a],a,[a])]
contexts = \xs -> go id xs
  where
  go prefix = \case
    [] -> []
    x:xs -> (prefix,x,xs) : go (prefix . (x:)) xs

slots :: [a] -> [([a] -> [a],[a])]
slots = \xs -> (id,xs) : go id xs
  where
  go prefix = \case
    [] -> []
    x:xs -> (prefix',xs) : go prefix' xs
      where
      prefix' = prefix . (x:)

foldHalves :: (a -> a -> a) -> a -> [a] -> a
foldHalves o z = \xs -> if null xs then z else go xs
  where
  go = \case
    [x] -> x
    xs -> go l `o` go r
      where
      (l,r) = splitAt (length xs `div` 2) xs

-- ASSUMPTION: k > 0
matches :: Int -> [ExpQ] -> [MatchQ]
matches k es =
     [ match (numP i) (normalB e) noWhere | i <- [1..k-1] | e <- tail es ]
  ++
     [ match wildP (normalB (head es)) noWhere ]

either1 :: (f a -> r) -> (g a -> r) -> (f :+: g) a -> r
{-# INLINE either1 #-}
either1 = \l r -> \case
  L1 x -> l x
  R1 x -> r x
