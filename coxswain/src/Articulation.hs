module Articulation (
  Articulation(..),
  ) where

import NormalForms (Col)

import GHCAPI (Kind,TcTyVar)

-- | The key to unifying row types is the articulation of row
-- variables: i.e. replacing a row variable at the root of a row with
-- a fresh variable, and unifying that fresh variable with the
-- necessary extension of the old root.
data Articulation =
  MkArticulation !TcTyVar !TcTyVar ![(Kind,Kind,Col)]
  -- ^ @q ~ q' .& ...@
