-- An inference that requires articulation.

{-# LANGUAGE DataKinds #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))

f :: Lacks p 0 => Proxy (p .& 0 .= a) -> ()
f _ = ()

g :: Lacks p 1 => Proxy (p .& 1 .= [b]) -> ()
g _ = ()

h p = f p `seq` g p

main :: IO ()
main = return $ h (Proxy :: Proxy (Row0 .& 0 .= () .& 1 .= [()]))
