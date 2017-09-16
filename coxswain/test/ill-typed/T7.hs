-- Lacks requires the specified label to not be in the record.

import Coxswain
import Data.Proxy (Proxy(..))

f :: forall p. Lacks (p .& () .= ()) () => Proxy p -> ()
f _ = ()

main :: IO ()
main = return $ f Proxy
