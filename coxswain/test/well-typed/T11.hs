-- Well-typedess requires simplifying derived constraints arising from
-- the unification in h of the domains of f and g. Specifically:
-- ignoring those derived constraints causes an amibiguity check
-- failure.
--
-- [D] _ {1}:: ((p0_a4QC[tau:2] .& (0 .= a0_a4QD[tau:2])) :: Row Nat *) ~# ((p1_a4QG[tau:2] .& (1 .= [b0_a4QH[tau:2]])) :: Row Nat *) (CNonCanonical)
-- [D] _ {1}:: (((q_a4Qv[sk:2] .& (0 .= y_a4Qw[sk:2])) .& (1 .= [z_a4Qx[sk:2]])) :: Row Nat *) ~# ((p0_a4QG[tau:2] .& (1 .= [b0_a4QH[tau:2]])) :: Row Nat *) (CNonCanonical)]

{-# LANGUAGE DataKinds #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))
import GHC.TypeLits (Nat)

f :: Lacks p 0 => Proxy (p .& 0 .= a) -> ()
f _ = ()

g :: Lacks p 1 => Proxy (p .& 1 .= [b]) -> ()
g _ = ()

h :: (Lacks q 0,Lacks q 1) => Proxy (q .& 0 .= y .& 1 .= [z]) -> ()
h p = f p `seq` g p

main :: IO ()
main = return $ h (Proxy :: Proxy (Row0 .& 0 .= () .& 1 .= [()]))
