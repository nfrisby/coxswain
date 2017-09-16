-- This test fails if we don't thaw Raw skolems:
--
-- Could not deduce: (q0 .& (B .= ())) ~ p from the context: (p ~ (q .& (B .= ())), Lacks p l)
--
-- when checking for ambiguity of the DLacks data constructor, I
-- suppose.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))

data DLacks p l where
  DLacks :: (p ~ (q .& B .= ()),Lacks p l) => DLacks p l

forgetL :: DLacks p l -> Proxy p
forgetL _ = Proxy

f :: Lacks p A => Proxy p -> ()
f _ = ()

g :: DLacks (p .& B .= b) A -> ()
g d@DLacks = f (forgetL d)

main :: IO ()
main = return $ g (DLacks :: DLacks (Row0 .& B .= ()) A)

data A
data B
