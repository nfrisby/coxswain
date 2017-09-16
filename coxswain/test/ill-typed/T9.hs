-- A contradiction in an inferred type.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(..))

yesOne :: Proxy (p .& 1 .= ()) -> ()
yesOne _ = ()

rZero :: Proxy (Row0 .& 0 .= ())
rZero = Proxy

g () = yesOne rZero

main :: IO ()
main = return ()
