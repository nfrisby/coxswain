-- Lacks requires the specified label to not be in the record.

import Coxswain

f :: Lacks (Row0 .& Bool .= Bool .& () .= ()) Bool => ()
f = ()

main :: IO ()
main = return f
