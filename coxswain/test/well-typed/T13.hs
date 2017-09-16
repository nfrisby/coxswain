-- Inference that definitely involves a restriction skolem.

{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))

f :: (Lacks p 0,Lacks q 1,(p .& 0 .= ()) ~ (q .& 1 .= ())) => Proxy p -> Proxy q -> ()
f _ _ = ()

g x y = f x y
