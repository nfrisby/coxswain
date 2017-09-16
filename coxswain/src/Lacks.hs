{-# LANGUAGE LambdaCase #-}

module Lacks (
  shiftLacks,
  ) where

import Data.Word (Word16)

import GHCAPI (Kind,Type)
import LowLevel (detCmpType)
import NormalForms
import Simplify

-- | How to adjust the insertion offset when simplifying a @Lacks@
-- constraint.
shiftLacks :: Type -> (Kind,Kind,Col) -> Simplification Word16
shiftLacks l (_,_,col)
  | Col m _t <- col
  , Just cmp <- detCmpType m l
  = case notEQ cmp of
    -- Rule:
    --   Lacks (p .& l) l   -->   FALSE
    Nothing -> Contradiction
    -- Rule:
    --   Lacks (p .& m) l   -->   Lacks p m
    Just inequality -> Progress $ case inequality of
      LessThan -> 1
      GreaterThan -> 0

  | otherwise = Yield

data Inequality = LessThan | GreaterThan

notEQ :: Ordering -> Maybe Inequality
notEQ = \case
  LT -> Just LessThan
  EQ -> Nothing
  GT -> Just GreaterThan
