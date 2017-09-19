{-# LANGUAGE LambdaCase #-}

-- | GHC does a better job optimizing Core for these evidence terms
-- than it does for the @Integer@s evidencing the @KnownNat@
-- dictionaries.

module KnownNat16 (
  knownNat16EvTerm,
  knownNat16Type,
  ) where

import Data.Bits (finiteBitSize,testBit)
import Data.Word (Word16)

import E
import GHCAPI
import LowLevel

knownNat16Type :: E -> Type
knownNat16Type = mkTyConTy . classTyCon . knownNat16Cls

knownNat16EvTerm :: E -> Word16 -> EvTerm
knownNat16EvTerm e n = foldr cons nil bits
  where
  cast cls ev = coxFiatCast (mkTyConTy (classTyCon (cls e))) (knownNat16Type e) ev
  bits = dropLeadingZeros id id $ map (testBit n) [0..(finiteBitSize n-1)] {- MSB first -}
  nil = cast zeroCls $ EvDFunApp (zeroDFunId e) [] []
  cons bit sofar = cast cls $ EvDFunApp (dfunid e) [] [sofar]
    where
    cls = if bit then times2Plus1Cls else times2Cls
    dfunid = if bit then times2Plus1DFunId else times2DFunId

dropLeadingZeros :: ([Bool] -> [Bool]) -> ([Bool] -> [Bool]) -> [Bool] -> [Bool]
dropLeadingZeros acc1 acc2 = \case
  [] -> acc1 []
  bit:bits
    | bit -> dropLeadingZeros (acc1 . acc2 . (True:)) id bits
    | otherwise -> dropLeadingZeros acc1 (acc2 . (False:)) bits
