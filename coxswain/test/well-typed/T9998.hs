-- The plugin correctly reports a contradiction here, but GHC seems to
-- ignore it! More details from a conversation on ghc-devs:
{- Me:

I just realized that, according to
https://ghc.haskell.org/trac/ghc/wiki/Plugins/TypeChecker, "If the
plugin finds a contradiction amongst the givens, it should return
TcPluginContradiction containing the contradictory constraints. These
will turn into inaccessible code errors."

And the brief demo in my previous email seems to indicate that
"inaccessible code errors" are only realized as deferred type errors,
with no static manifestation.

-}
{- Edward Z. Yang:

While I am not 100% sure, I belive [sic] this is related to
the fact that currently inaccessible branches (a local
contradiction indicates inaccessibility) are not
being reported in GHC.  I reported this in
https://ghc.haskell.org/trac/ghc/ticket/12694
whose root cause was suggested might be
https://ghc.haskell.org/trac/ghc/ticket/12466

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=10 #-}

import Coxswain
import Data.Proxy (Proxy(..))

noZero :: Lacks p 0 => Proxy p -> ()
noZero _ = ()

rZero :: Proxy (Row0 .& 0 .= ())
rZero = Proxy

g () = noZero rZero

main :: IO ()
main = return ()
