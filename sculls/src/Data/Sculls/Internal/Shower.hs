module Data.Sculls.Internal.Shower where

-- | The @Bool@ is only @True@ for the leftmost argument of 'mappend'.
newtype Shower = MkShower {unShower :: Bool -> ShowS}

instance Monoid Shower where
  mempty = MkShower (const id)
  MkShower f `mappend` MkShower g = MkShower $ \frst -> f frst . g False

runShower :: Shower -> ShowS
runShower = ($ True) . unShower
