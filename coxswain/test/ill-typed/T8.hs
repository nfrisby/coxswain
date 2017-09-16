-- Well-typedess requires two articulations leading to non-trivial
-- unification of a shared column's types.
--
-- This would be well-typed, were it not for https://ghc.haskell.org/trac/ghc/ticket/10833

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))

type family T (a :: *) = (r :: *) | r -> a where

f :: ( (p .& 0 .= a) ~ (q .& 1 .= T b) , (p .& 2 .= c) ~ (r .& 1 .= T d) )
   => Proxy p -> Proxy q -> Proxy r -> Proxy a -> Proxy c -> b -> d
f _ _ _ _ _ x = x

main :: IO ()
main = return $ f Proxy Proxy Proxy Proxy Proxy ()
