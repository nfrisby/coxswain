-- Exercising local refinements of restriction skolems.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(..))
import GHC.TypeLits (Nat)

type One p = p .& 1 .= ()
type Two p = p .& 2 .= ()
type Eight p = p .& 8 .= ()
type Nine p = p .& 9 .= ()

-- Key property for test: the constraints of the two constructors
-- cannot hold simultaneously.
data H :: Row Nat * -> * where
  Has1 :: (Lacks q 1,Lacks q 2) => H (q .& 1 .= ())
  Has2 :: (Lacks q 1,Lacks q 2) => H (q .& 2 .= ())

expect :: Lacks p l => Proxy (l :: Nat) -> Proxy (p .& l .= ()) -> ()
expect _ _ = ()

-- Key property for test: the outer equality ensures that r and s are
-- both rewritten to extensions of a fresh restriction variable.
f :: forall r s. (Nine r ~ Eight s) => H r -> ()
f Has1 = expect (Proxy :: Proxy 1) (Proxy :: Proxy r)
f Has2 = expect (Proxy :: Proxy 2) (Proxy :: Proxy r)

main :: IO ()
main = return ()
