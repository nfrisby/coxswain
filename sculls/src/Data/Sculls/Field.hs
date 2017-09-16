{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Sculls.Field where

import GHC.Exts (Constraint)

-- | A constant whose type is independent of the field.
newtype C a (l :: kl) (t :: kt) = C {unC :: a}
  deriving (Eq,Ord,Monoid)

-- | The field's value.
newtype I (l :: k) t = I {unI :: t}
  deriving (Eq,Ord,Monoid)

-- | A dictionary for the field.
data D :: (kl -> kt -> Constraint) -> kl -> kt -> * where Dict :: c l t => D c l t

infixr 1 :->:

infixl 5 `unA`

-- | A function field.
newtype (f :->: g) (l :: kl) (t :: kt)= A {unA :: f l t -> g l t}

infixr 9 :.:

-- | A higher-order field.
newtype (f :.: g) (l :: kl) (t :: kt) = O {unO :: f l (g l t)}
deriving instance Eq (f l (g l t)) => Eq ((f :.: g) (l :: kl) (t :: kt))
deriving instance Ord (f l (g l t)) => Ord ((f :.: g) (l :: kl) (t :: kt))
deriving instance Monoid (f l (g l t)) => Monoid ((f :.: g) (l :: kl) (t :: kt))

-- | A functor for the field's value.
newtype F f (l :: kl) (t :: kt) = F {unF :: f t}
deriving instance Eq (f t) => Eq (F f (l :: kl) (t :: kt))
deriving instance Ord (f t) => Ord (F f (l :: kl) (t :: kt))
deriving instance Monoid (f t) => Monoid (F f (l :: kl) (t :: kt))

-----

instance Show a => Show (C a (l :: kl) (t :: kt)) where
  showsPrec d = showsPrec d . unC

instance Show t => Show (I (l :: k) t) where
  showsPrec d = showsPrec d . unI

instance Show (f l (g l t)) => Show ((f :.: g) (l :: kl) (t :: kt)) where
  showsPrec d = showsPrec d . unO

instance Show (f t) => Show (F f (l :: kl) (t :: kt)) where
  showsPrec d = showsPrec d . unF

-----

getC :: proxy (l :: k) -> C a l t -> a
getC _ = unC

getI :: proxy (l :: k) -> I l t -> t
getI _ = unI

getF :: proxy (l :: k) -> F f l t -> f t
getF _ = unF

putC :: proxy (l :: k) -> a -> C a l t
putC _ = C

putI :: proxy (l :: k) -> t -> I l t
putI _ = I

putF :: proxy (l :: k) -> f t -> F f l t
putF _ = F
