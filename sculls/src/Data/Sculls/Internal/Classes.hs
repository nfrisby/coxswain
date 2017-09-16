{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Sculls.Internal.Classes where

import GHC.Exts (Constraint,Proxy#,proxy#)
import GHC.TypeLits (KnownSymbol,Symbol,symbolVal')

-- | For use with 'rdictCol' -- see 'rdict'.
class    c t => OnColType (c :: kt -> Constraint) (l :: kl) (t :: kt)
instance c t => OnColType (c :: kt -> Constraint) (l :: kl) (t :: kt)

-- | For use with 'rdictCol' -- see 'rdictField'.
class    c (f l t) => OnField (c :: * -> Constraint) (f :: kl -> kt -> *) (l :: kl) (t :: kt)
instance c (f l t) => OnField (c :: * -> Constraint) (f :: kl -> kt -> *) (l :: kl) (t :: kt)

-----

-- | For showing fields and their column's name.
class    (KnownSymbol (ColSymbol l),Show (f l t)) => ShowCol f (l :: kl) (t :: kt)
instance (KnownSymbol (ColSymbol l),Show (f l t)) => ShowCol f (l :: kl) (t :: kt)

-- | How to render a column name as a 'Symbol'.
type family ColSymbol (l :: kl) :: Symbol

type instance ColSymbol (s :: Symbol) = s

-- | Render the column name via 'ColSymbol'.
showsColName :: forall l. KnownSymbol (ColSymbol l) => Proxy# (l :: kl) -> ShowS
showsColName = \_ -> showString (symbolVal' (proxy# :: Proxy# (ColSymbol l)))
