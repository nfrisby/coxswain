-- Normal form is independent of the order of row extensions.

import Coxswain

f :: (Normalize (Row0 .& 0 .= () .& 1 .= ()) ~ Normalize (Row0 .& 1 .= () .& 0 .= ())) => ()
f = ()

main :: IO ()
main = return f
