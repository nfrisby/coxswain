-- Exercising local assumptions.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality
import GHC.TypeLits (Nat)

data Zero :: Row Nat * -> * where
  No :: Lacks p 0 => Zero p
  Yes :: Lacks q 0 => Zero (q .& 0 .= ())

f :: Lacks r 3 => Zero r -> ()
f No = ()
f Yes = ()
