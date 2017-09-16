module Data.Sculls.Record (
  -- * Record type
  R,
  -- ** Construction
  (.*),
  mkR,
  rhas,
  rdict,
  rdictCol,
  rdictField,
  rintro,
  rpure,
  -- ** Observers
  (./),
  (./*),
  relim,
  rlens,
  rsel,
  runcons,
  rvariants,
  -- ** Compositions
  rmap,(/$\),
  rsplat,(/*\),
  -- ** Traversals
  rfold,
  rtraverse,
  -- ** Classes
  RAll,
  Short,
  -- * Field types
  module Data.Sculls.Field,
  -- * Row types
  module Coxswain,
  ) where

import Coxswain
import Data.Sculls.Field
import Data.Sculls.Internal.RecordAndVariant
import Data.Sculls.Internal.ShortVector (Short)
