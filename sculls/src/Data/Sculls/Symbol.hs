{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=Coxswain #-}

-- | "Data.Sculls" along with the 'dot', 'Data.Sculls.Label..=', and
-- 'inj' functions and 'IsLabel' instance for using
-- 'GHC.TypeLits.Symbol' as the column name kind with the @#foo@
-- syntax.
--
-- For example, importing this module with @-XOverloadedLabels@ and
-- @-fplugin=Coxswain@ should be enough for the following:
--
-- > *> :t mkR .* #foo .= 3 .* #bar .= "baz"
-- > mkR .* #foo .= 3 .* #bar .= "baz"
-- >   :: Num t => R I ((Row0 .& ("foo" .= t)) .& ("bar" .= [Char]))
-- > *> mkR .* #foo .= 3 .* #bar .= "baz"
-- > {(bar="baz") (foo=3)}

module Data.Sculls.Symbol (
  module Data.Sculls,
  module Data.Sculls.Symbol,
  ) where

import Coxswain
import GHC.OverloadedLabels (IsLabel(..))
import GHC.TypeLits (Symbol)

import Data.Sculls

-- | A proxy for labels.
data L (s :: Symbol) = MkL

-- | Define 'L' as an overloaded label for the @#foo@ syntax.
instance (s ~ x) => IsLabel x (L s) where fromLabel = MkL

infix 3 .=

-- | Build a column from a label and value.
--
-- @(.=) = const 'I'@
(.=) :: L l -> t -> I l t
(.=) = const I

infixl 8 `dot`

-- | Select a fields's value.
--
-- @dot = \\r l -> 'getI' l ('rsel' r)@
dot :: (Lacks p l,Short (NumCols p)) => R I (p .& l .= t) -> L l -> t
dot = \r l -> getI l (rsel r)

-- | An ascription, for use with './' and '.+'.
--
-- @idL = id@
idL :: L s -> L s
idL = id

-- | Create a variant.
--
-- @inj = \\l t -> mkV (putI l t)@
inj :: Lacks p l => L l -> t -> V I (p .& l .= t)
inj = \l t -> mkV (putI l t)
