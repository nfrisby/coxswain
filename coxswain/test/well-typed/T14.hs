-- Inference that definitely involves a restriction skolem, with
-- nested givens via a GADT pattern.

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))
import Data.Type.Equality

f :: (Lacks p 0,Lacks q 1,(p .& 0 .= ()) ~ (q .& 1 .= ())) => Proxy p -> Proxy q -> z :~: y -> ()
f _ _ Refl = ()

g x y = f x y
