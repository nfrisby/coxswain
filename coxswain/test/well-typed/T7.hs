-- Lacks requires the specified label to not be in the record.

import Coxswain
import Data.Proxy (Proxy(Proxy))

f :: Lacks (p .& () .= ()) Bool => Proxy p -> ()
f _ = ()

main :: IO ()
main = return $ f (Proxy :: Proxy Row0)
