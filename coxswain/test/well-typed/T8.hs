-- Well-typedess requires two articulations leading to unification of
-- a shared column's types.

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))

f :: ( (p .& 0 .= a) ~ (q .& 1 .= b) , (p .& 2 .= c) ~ (r .& 1 .= d) )
   => Proxy p -> Proxy q -> Proxy r -> Proxy a -> Proxy c -> b -> d
f _ _ _ _ _ x = x

main :: IO ()
main = return $ f Proxy Proxy Proxy Proxy Proxy ()
