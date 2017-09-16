module Data.Sculls.Variant (
  -- * Variant type
  V,
  -- ** Construction
  (.+),
  mkV,
  rvariants,
  vintro,
  vone,
  -- ** Observers
  (.-),
  (.-+),
  vabsurd,
  vconstant,
  velim,
  vpartition,
  vproof,
  vsingleton,
  -- * Field types
  module Data.Sculls.Field,
  -- * Row types
  module Coxswain,
  ) where

import Coxswain
import Data.Sculls.Field
import Data.Sculls.Internal.RecordAndVariant
