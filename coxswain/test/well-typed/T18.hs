-- Some TypeNat simplifications.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(..))
import GHC.Exts
import GHC.TypeLits

x :: Proxy p -> Proxy (NumCols p + 1)
x _ = Proxy

y :: Proxy p -> Proxy (3 + NumCols p - 2)
y _ = Proxy

main :: IO ()
main = return $ (x p `asTypeOf` y p) `seq` ()
  where
  p = Proxy :: Proxy (Any :: Row * *)
