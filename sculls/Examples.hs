{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=Coxswain #-}

{-# OPTIONS_GHC -fplugin-opt=Coxswain:logfile=dump.hs #-}
{-# OPTIONS_GHC -fplugin-opt=Coxswain:trace #-}

{-# OPTIONS_GHC -fplugin-opt=Coxswain:foo -fplugin-opt=Coxswain:baaz -fplugin-opt=Coxswain:bar #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

module Main where

import Data.Sculls.Symbol
import Data.Proxy
import GHC.TypeLits

-- Named Arguments

quadraticRoots :: R I (Row0 .& "a" .= Double .& "b" .= Double .& "c" .= Double) -> (Double,Double)
quadraticRoots r = quadraticRootsX (r :: R I (Row0 .& "a" .= Double .& "b" .= Double .& "c" .= Double))

quadraticRootsX ::
     ( Floating a
     , Short (NumCols rho + 2)
     , Lacks rho "a"
     , Lacks rho "b"
     , Lacks rho "c"
     )
  => R I (rho .& "a" .= a .& "b" .= a .& "c" .= a) -> (a,a)
{-# INLINE quadraticRootsX #-}
quadraticRootsX coeffs =
  ((-b + term2) / (2*a),(-b - term2) / (2*a))
  where
  term2 = sqrt (b ^ 2 - 4 * a * c)

  a = coeffs `dot` #a
  b = coeffs `dot` #b
  c = coeffs `dot` #c

-- | Solve equation using Newton-Raphson iterations.
--
-- This method require both initial guess and bounds for root. If
-- Newton step takes us out of bounds on root function reverts to
-- bisection.
newtonRaphson
  :: Double
     -- ^ Required precision
  -> (Double,Double,Double)
  -- ^ (lower bound, initial guess, upper bound). Iterations will no
  -- go outside of the interval
  -> (Double -> (Double,Double))
  -- ^ Function to finds roots. It returns pair of function value and
  -- its derivative
  -> Double
newtonRaphson = undefined

-- | Solve equation using Newton-Raphson iterations.
--
-- This method require both initial guess and bounds for root. If
-- Newton step takes us out of bounds on root function reverts to
-- bisection.
newtonRaphson2 ::
     R I (Row0
     .& "precision" .= Double
     .& "lowerbound" .= Double
     .& "guess0" .= Double
     .& "upperbound" .= Double
     )
     -- ^ Required precision. Iterations will no go outside of the interval.
  -> (Double -> (Double,Double))
  -- ^ Function to finds roots. It returns pair of function value and
  -- its derivative
  -> Double
newtonRaphson2 = undefined

-----

vars :: [V I (Row0 .& "x" .= Int .& "y" .= Char .& "z" .= Bool)]
vars = [inj #z True,inj #x 7,inj #y 'h',inj #z False,inj #y 'i',inj #x 3]

pvars :: R (F []) (Row0 .& "x" .= Int .& "y" .= Char .& "z" .= Bool)
pvars = vpartition vars

-----

main :: IO ()
main = do
  let binom = mkR .* #c .= -3 .* #a .= 1 .* #b .= -2
  print $ quadraticRoots binom
  print $ quadraticRoots (binom ./* #c .= 1)
  print $ quadraticRootsX (binom .* #note .= "This is a boring polynomial.")
  print pvars
