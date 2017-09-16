-- Possible GHC bug?
--
-- Yes, indeed: https://ghc.haskell.org/trac/ghc/ticket/10833

{-# LANGUAGE TypeFamilyDependencies #-}

import Data.Proxy (Proxy(Proxy))

type family T (a :: *) = (r :: *) | r -> a where

f :: ( T a ~ T b ) => a -> b
f x = x
