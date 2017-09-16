{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Coxswain (
  -- * Columns
  Col,
  type (.=),

  -- * Rows
  Row,
  Row0,
  type (.&),
  Ext,

  -- * Lacks constraints
  Lacks,
  RowInsertionOffset,
  unRowInsertionOffset,
  rowInsertionOffset,
  rowInsertionOffsetEv,

  -- * Length abstraction
  NumCols,

  -- * Normalized rows
  NRow(..),
  Normalize,

  -- * Evidence
  HasRestriction(..),
  HasCol(..),
  HasSomeCol(..),

  -- * Plugin
  plugin
  ) where

import Data.Bits ((.|.),unsafeShiftL)
import Data.Kind (Type)
import Data.Word (Word16)
import GHC.Exts (Proxy#)
import GHC.TypeLits

import Plugin (plugin)

-----

infix 3 .=

-- | Column kind.
--
-- Use the '.=' type family to construct this kind. (Always! Always,
-- avoid variables of kind 'Col'.)
data Col (kl :: Type) (kt :: Type)

-- | Column constructor.
--
-- The plugin does not implement eta-expansion, so it's best to always
-- write @l '.=' t@ instead of @gamma :: 'Col' k@.
type family (l :: kl) .= (t :: kt) = (col :: Col kl kt) | col -> l t where

-----

-- | Row kind.
--
-- Use the 'Row0' and '.&' type families to construct this kind.
data Row (kl :: Type) (kt :: Type)

-- | The empty row.
type family Row0 :: Row kl kt where

infixl 2 .&

-- | Row extension.
--
-- This family has non-trivial injectivity, which the plugin
-- implements. In particular:
--
-- > p .& l .= t ~ q .& l .= s   ==>  p ~ q , t ~ s
-- >
-- > p .& l .= t ~ p .& m .= s   ==>  l ~ m, t ~ s
type family (p :: Row kl kt) .& (col :: Col kl kt) = (q :: Row kl kt) where

-- | A synonym for avoiding @-XTypeOperators@.
type Ext p l t = p .& (l .= t)

-----

-- | Evidence of a 'Lacks' constraint.
newtype RowInsertionOffset (p :: Row kl kt) (l :: kl) = MkRowInsertionOffset {unRowInsertionOffset :: Word16}

-- | The lacks predicate.
class Lacks (p :: Row kl kt) (l :: kl) where
  rowInsertionOffset_ :: RowInsertionOffset p l

-- | Returns the index in the normal form of @p@ at which @l@ would be
-- inserted.
rowInsertionOffset :: forall (p :: Row kl kt) l. Lacks p l => Proxy# p -> Proxy# l -> Word16
{-# INLINE rowInsertionOffset #-}
rowInsertionOffset _ _ = unRowInsertionOffset (rowInsertionOffset_ :: RowInsertionOffset p l)

-- | Returns evidence for the index in the normal form of @p@ at which
-- @l@ would be inserted.
rowInsertionOffsetEv :: Lacks (p :: Row kl kt) l => RowInsertionOffset p l
{-# INLINE rowInsertionOffsetEv #-}
rowInsertionOffsetEv = rowInsertionOffset_

-----

infixl 2 `NExt`

-- | A normalized row.
--
-- The following invariant is intended, and it is ensured by the
-- 'Normalize' type family. INVARIANT: The columns are sorted
-- ascending with respect to an arbitrary total order on the column
-- names.
data NRow kl kt =
    NRow0  -- ^ The empty row.
  |
    NExt (NRow kl kt) kl kt   -- ^ A row extension.

-- | Normalize a row.
--
-- Note that the plugin can only reduce this family once all labels of
-- the 'Row' argument are known.
type family Normalize (p :: Row kl kt) = (q :: NRow kl kt) | q -> p where

-- | The number of columns in a row.
--
-- The plugin reduces this family eagerly, as much as possible as soon
-- as possible. In particular, @NumCols (p .& l .= t)@ reduces to
-- @NumCols p + 1@.
type family NumCols (p :: Row kl kt) :: Nat where

-----

-- | @HasRestriction p q l t@ evidences that @p@ is @q@ extended with
-- @l '.=' t@.
data HasRestriction :: Row kl kt -> Row kl kt -> kl -> kt -> * where
  HasRestriction :: Lacks q l => HasRestriction (q .& l .= t) q l t

-- | @HasCol p l t@ evidences that there exists a @q@ such that @p@ is
-- @q@ extended with @l '.=' t@.
data HasCol :: Row kl kt -> kl -> kt -> * where
  HasCol :: Lacks q l => HasCol (q .& l .= t) l t

-- | @HasSomeCol p@ evidences that @p@ is some row extension.
data HasSomeCol :: Row kl kt -> * where
  HasSomeCol :: Proxy# q -> Proxy# l -> Proxy# t -> HasSomeCol (q .& l .= t)

-----

-- | This type family only appears in error messages. The first
-- argument will be a row variable from a type signature and the
-- second argument will be a list of column names; the application
-- represents the row restriction that removes those columns from that
-- row variable.
type family Restriction (p :: Row kl kt) (ls :: Row kl kt) :: Row kl kt where

-----

class Lacks_Zero (l :: kl) where
  rowInsertionOffset_Zero :: RowInsertionOffset (Row0 :: Row kl kt) l
instance Lacks_Zero (l :: kl) where
  {-# INLINE rowInsertionOffset_Zero #-}
  rowInsertionOffset_Zero = MkRowInsertionOffset 0

class Lacks_Plus (p :: Row kl kt) (l :: kl) where
  rowInsertionOffset_Plus :: RowInsertionOffset p l
-- The plugin coerces this dictionary in order to increase the offset
-- when simplifying wanted Lacks constraints.
instance (Lacks p l,KnownNat16) => Lacks_Plus (p :: Row kl kt) l where
  {-# INLINE rowInsertionOffset_Plus #-}
  rowInsertionOffset_Plus = case rowInsertionOffset_ :: RowInsertionOffset p l of
    MkRowInsertionOffset o -> MkRowInsertionOffset (o + natVal16)

class Lacks_Minus (p :: Row kl kt) l where
  rowInsertionOffset_Minus :: RowInsertionOffset p l
-- The plugin coerces this dictionary in order to decrease the offset
-- when simplifying given Lacks constraints.
instance (Lacks p l,KnownNat16) => Lacks_Minus (p :: Row kl kt) l where
  {-# INLINE rowInsertionOffset_Minus #-}
  rowInsertionOffset_Minus = case rowInsertionOffset_ :: RowInsertionOffset p l of
    MkRowInsertionOffset o -> MkRowInsertionOffset (o - natVal16)

-----

class CoxswainWorking (phase :: Nat)

class Ren (a :: k) (b :: k)

class KnownNat16 where natVal16 :: Word16

class Zero where zero :: Word16
instance Zero where zero = 0

class Times2Plus1 where times2Plus1 :: Word16
instance KnownNat16 => Times2Plus1 where times2Plus1 = 1 .|. unsafeShiftL natVal16 1

class Times2 where times2 :: Word16
instance KnownNat16 => Times2 where times2 = unsafeShiftL natVal16 1
