-- An empty row can never equal a non-empty row.

import Coxswain

f :: (Row0 ~ (Row0 .& () .= ())) => ()
f = ()

main :: IO ()
main = return f
