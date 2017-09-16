{-# LANGUAGE Rank2Types #-}

-- | A few basic excerpts from SYB.

module MiniSYB (module MiniSYB,cast,gmapM) where

import Data.Data (Data,gmapM)
import Data.Typeable (Typeable,cast,gcast)

newtype M m x = M { unM :: x -> m x }

ext0 :: (Typeable a,Typeable b) => c a -> c b -> c a
ext0 def ext = maybe def id (gcast ext)

extM ::
     (Monad m,Typeable a,Typeable b)
  => (a -> m a) -> (b -> m b) -> a -> m a
extM def ext = unM ((M def) `ext0` (M ext))

mkM ::
     (Monad m,Typeable a,Typeable b)
  => (b -> m b) -> a -> m a
mkM = extM return

topDownM :: (Data a,Monad m) => (forall b. Data b => b -> m b) -> a -> m a
topDownM f x = f x >>= gmapM (topDownM f)
