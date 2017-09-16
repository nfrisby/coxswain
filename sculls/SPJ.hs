{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=Coxswain #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

module SPJ (f,fmono) where

import Data.Functor.Identity (Identity(..))

import Data.Sculls.Symbol
import GHC.TypeLits (type (+))

upd :: I "f" Int -> I "f" Int
upd (I x) = I (x + 1)

f ::
    ( Lacks r "f"
    , Short (NumCols r) )
  => R I (r .& "f" .= Int)
  -> R I (r .& "f" .= Int)
f = over rlens upd

-- or: f r = r ./* #f .= (1 + r `dot` #f), but the Core is worse

fmono ::
     R I (Row0 .& "a" .= a .& "b" .= b .& "c" .= c .& "f" .= Int)
  -> R I (Row0 .& "a" .= a .& "b" .= b .& "c" .= c .& "f" .= Int)
fmono = f


-----

over :: ((a -> Identity b) -> s -> Identity t) -> (a -> b) -> s -> t
over l f = runIdentity . l (Identity . f)
{-# INLINE over #-}
