{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fplugin=Coxswain #-}
{-# OPTIONS_GHC -fplugin-opt=Coxswain:trace #-}
{-# OPTIONS_GHC -fplugin-opt=Coxswain:logfile=dump.hs #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

module Data.Sculls.Internal.RecordAndVariant where

import Coxswain
import qualified Data.Foldable as Foldable
import Data.Functor.Identity
import Data.Proxy (Proxy(Proxy))
import Data.Semigroup (Semigroup((<>)))
import qualified Data.Traversable as Traversable
import Data.Word (Word16)
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (Any,Constraint,Proxy#,proxy#)
import qualified GHC.Generics as G
import GHC.Show (appPrec1)
import GHC.TypeLits (type (-),type (+),Nat,Symbol)
import Unsafe.Coerce (unsafeCoerce)

import Data.Sculls.Field
import Data.Sculls.Internal.Classes
import Data.Sculls.Internal.RecordAndVariantTH
import Data.Sculls.Internal.ShortVector
import Data.Sculls.Internal.Shower

------------------------------

-- | A record type.
--
-- There is a somewhat arbitrary limit on the supported number of
-- fields
newtype R (f :: kl -> kt -> *) (p :: Row kl kt) = MkR (SV (NumCols p) Any)

instance RAll (ShowCol f) p => Show (R f (p :: Row kl kt)) where
  {-# INLINE showsPrec #-}
  showsPrec _ r = braced $ runShower fieldsShower
    where
    braced x = showChar '{' . x . showChar '}'

    fieldsShower = rfold $ fieldShower /$\ rdictCol proxy# /*\ r

    fieldShower :: forall (l :: kl) (t :: kt). (D (ShowCol f) :->: f :->: C Shower) l t
    {-# INLINE fieldShower #-}
    fieldShower = A $ \Dict -> A $ \flt -> C $ MkShower $ \frst ->
        (if frst then id else showChar ' ')
      .
        showParen True (
          showsColName (proxy# :: Proxy# l)
        .
          showChar '='
        .
          showsPrec 0 flt
        )

instance RAll (OnField Monoid f) p => Monoid (R f (p :: Row kl kt)) where
  {-# INLINE mempty #-}
  mempty = f /$\ rdictCol proxy#
    where
    f :: forall (l :: kl) (t :: kt). (D (OnField Monoid f) :->: f) l t
    {-# INLINE f #-}
    f = A $ \Dict -> mempty
  {-# INLINE mappend #-}
  mappend = \l r -> f /$\ rdictCol proxy# /*\ l /*\ r
    where
    f :: forall (l :: kl) (t :: kt). (D (OnField Monoid f) :->: f :->: f :->: f) l t
    {-# INLINE f #-}
    f = A $ \Dict -> A $ \l -> A $ \r -> mappend l r

instance RAll (OnField Semigroup f) p => Semigroup (R f (p :: Row kl kt)) where
  {-# INLINE (<>) #-}
  (<>) = \l r -> f /$\ rdictCol proxy# /*\ l /*\ r
    where
    f :: forall (l :: kl) (t :: kt). (D (OnField Semigroup f) :->: f :->: f :->: f) l t
    {-# INLINE f #-}
    f = A $ \Dict -> A $ \l -> A $ \r -> l <> r

-- | Empty record.
mkR :: R f (Row0 :: Row kl kt)
{-# INLINE mkR #-}
mkR = MkR V0

-- | Field selection.
rsel :: forall f (p :: Row kl kt) l t. (Short (NumCols p),Lacks p l) => R f (p .& l .= t) -> f l t
{-# INLINE rsel #-}
rsel = \(MkR sv) -> unsafeCoerce $ select sv $ rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)

infixl 1 .* , ./ , ./*

-- | Record extension.
(.*) :: forall f (p :: Row kl kt) l t. (Short (NumCols p),Lacks p l) => R f p -> f l t -> R f (p .& l .= t)
{-# INLINE (.*) #-}
(.*) = \(MkR sv) a -> MkR $ extend sv (unsafeCoerce a) (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l))

-- | Record restriction.
(./) :: forall f (p :: Row kl kt) proxy l t. (Short (NumCols p),Lacks p l) => R f (p .& l .= t) -> proxy l -> R f p
{-# INLINE (./) #-}
(./) = \(MkR sv) _ -> MkR $ snd (restrict sv (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)))

-- | Record update using conventional record primitives.
(./*) :: forall f (p :: Row kl kt) l t1 t2. (Short (NumCols p),Lacks p l) => R f (p .& l .= t1) -> f l t2 -> R f (p .& l .= t2)
{-# INLINE (./*) #-}
(./*) = \r col -> let
  f :: f l t1 -> f l t2
  f = const col
  in runIdentity $ rlens (Identity . f) r

-- | Record update using conventional record primitives.
_update :: forall f (p :: Row kl kt) l t1 t2. (Short (NumCols p),Lacks p l) => R f (p .& l .= t1) -> f l t2 -> R f (p .& l .= t2)
{-# INLINE _update #-}
_update = \r col -> r ./ (Proxy :: Proxy l) .* col

-- | Record lens using conventional record primitives.
_rlens ::
  forall g f (p :: Row kl kt) l t1 t2.
     (Functor g,Lacks p l,Short (NumCols p))
  => (f l t1 -> g (f l t2)) -> R f (p .& l .= t1) -> g (R f (p .& l .= t2))
{-# INLINE _rlens #-}
_rlens = \f r -> (\x -> r ./ (Proxy :: Proxy l) .* unsafeCoerce (x :: f l t2)) <$> f (unsafeCoerce (rsel r :: f l t1))

-- | Record lens.
rlens ::
  forall g f (p :: Row kl kt) l t1 t2.
     (Functor g,Lacks p l,Short (NumCols p))
  => (f l t1 -> g (f l t2)) -> R f (p .& l .= t1) -> g (R f (p .& l .= t2))
{-# INLINE rlens #-}
rlens = \f (MkR sv) -> MkR <$> lensSV (unsafeCoerce f) sv (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l))

-- | Split a record into a field the rest of the record.
--
-- > runcons r = (rsel r,r ./ (proxy# :: Proxy# l))
runcons :: forall f (p :: Row kl kt) l t. (Short (NumCols p),Short (NumCols p + 1),Lacks p l) => R f (p .& l .= t) -> (f l t,R f p)
{-# INLINE runcons #-}
runcons r = (rsel r,r ./ (Proxy :: Proxy l))

-----

-- | Record of evidence that each column exists in the record's row.
rhas :: forall p. Short (NumCols p) => R (HasCol p) p
{-# INLINE rhas #-}
rhas = MkR $ unsafeCoerce fakeHasCol <$> indices @(NumCols p)

newtype SadCoercion1 (p :: Row kl kt) l r = MkSadCoercion1 (Lacks p l => r)
newtype SadCoercion2 r = MkSadCoercion2 (Word16 -> r)

-- ASSUMPTION: Word16 and a Lacks dict are coercible
unsafeWithLacks :: forall p l r. Proxy# p -> Proxy# l -> Word16 -> (Lacks (p :: Row kl kt) l => r) -> r
{-# INLINE unsafeWithLacks #-}
unsafeWithLacks _ _ w k = let MkSadCoercion2 x = unsafeCoerce (MkSadCoercion1 @p @l @r k) in x w

mkHasRestriction :: Lacks (q :: Row kl kt) l => p :~: (q .& l .= t) -> HasRestriction p q l t
{-# INLINE mkHasRestriction #-}
mkHasRestriction Refl = HasRestriction

fakeHasCol :: forall (p :: Row kl kt) l t. Word16 -> HasCol p l t
{-# INLINE fakeHasCol #-}
fakeHasCol fin = cnv hasres
  where
  cnv :: forall q. HasRestriction p q l t -> HasCol p l t
  {-# INLINE cnv #-}
  cnv HasRestriction = HasCol

  hasres :: forall q. HasRestriction p q l t
  {-# INLINE hasres #-}
  hasres =
    unsafeWithLacks (proxy# :: Proxy# q) (proxy# :: Proxy# l) fin
      (mkHasRestriction (unsafeCoerce (Refl :: () :~: ())))

-----

-- | Record analog of 'pure'.
rpure :: Applicative (SV (NumCols p)) => (forall (l :: kl) (t :: kt). f l t) -> R f p
{-# INLINE rpure #-}
rpure f = MkR $ pure $ unsafeCoerce (f @Any)

infixl 4 /$\ , `rmap` , /*\ , `rsplat`

-- | Record analog of 'fmap'.
rmap :: Functor (SV (NumCols p)) => (forall (l :: kl) (t :: kt). (a :->: b) l t) -> R a p -> R b p
{-# INLINE rmap #-}
rmap f (MkR a) = MkR (unsafeCoerce (f @Any) <$> a)

-- | @(/$\\) = 'rmap'@
(/$\) :: Applicative (SV (NumCols p)) => (forall (l :: kl) (t :: kt). (a :->: b) l t) -> R a p -> R b p
{-# INLINE (/$\) #-}
(/$\) = rmap

-- | Record analog of '<*>'.
rsplat :: Applicative (SV (NumCols p)) => R (a :->: b) p -> R a p -> R b p
{-# INLINE rsplat #-}
rsplat (MkR f) (MkR a) = MkR (unsafeCoerce f <*> a)

-- | @(/*\\) = 'rsplat'@
(/*\) :: Applicative (SV (NumCols p)) => R (a :->: b) p -> R a p -> R b p
{-# INLINE (/*\) #-}
(/*\) = rsplat

-----

-- | Combine all the fields' values. Beware that the fields are
-- combined in an arbitrary order!
rfold :: forall m p. (Foldable (SV (NumCols p)),Monoid m) => R (C m) p -> m
{-# INLINE rfold #-}
rfold (MkR sv) = Foldable.fold (unsafeCoerce sv :: SV (NumCols p) m)

-- | Traverse all the fields. Beware that the fields are visited in an
-- arbitrary order!
rtraverse :: forall f g h p. (Applicative g,Traversable (SV (NumCols p))) => (forall (l :: kl) (t :: kt). (f :->: F g :.: h) l t) -> R f p -> g (R h p)
{-# INLINE rtraverse #-}
rtraverse f (MkR sv) = unsafeCoerce $ Traversable.traverse (unsafeCoerce (f @Any @Any) :: Any -> g Any) sv

-----

-- | A record of dictionaries for the binary predicate @c@ on column
-- name and column type.
rdictCol :: forall c (p :: Row kl kt). RAll c p => Proxy# c -> R (D c) p
{-# INLINE rdictCol #-}
rdictCol _ = MkR $ rdict_ (proxy# :: Proxy# c) (proxy# :: Proxy# p)

-- | A record of dictionaries for the unary predicate @c@ on column
-- types.
rdict :: forall c (p :: Row kl kt). RAll (OnColType c) p => Proxy# c -> R (D (OnColType c)) p
{-# INLINE rdict #-}
rdict _ = rdictCol (proxy# :: Proxy# (OnColType c))

-- | A record of dictionaries for the unary predicate @c@ on field
-- types.
rdictField :: forall c (p :: Row kl kt) f. RAll (OnField c f) p => Proxy# c -> Proxy# f -> R (D (OnField c f)) p
{-# INLINE rdictField #-}
rdictField _ _ = rdictCol (proxy# :: Proxy# (OnField c f))

-- | The constraint @c l t@ holds for /all/ columns @l '.=' t@ in the
-- row @p@.
class    (Short (NumCols p - 1),RAll2 c (Normalize p) (NumCols p)) => RAll (c :: kl -> kt -> Constraint) (p :: Row kl kt) where
  rdict_ :: Proxy# c -> Proxy# p -> SV (NumCols p) Any
instance (Short (NumCols p - 1),RAll2 c (Normalize p) (NumCols p)) => RAll (c :: kl -> kt -> Constraint) (p :: Row kl kt) where
  {-# INLINE rdict_ #-}
  rdict_ c _ = rdict_2 c (proxy# :: Proxy# (Normalize p)) (proxy# :: Proxy# (NumCols p))

-- | Evidence of @c@ for each column.
class Short n => RAll2 (c :: kl -> kt -> Constraint) (p :: NRow kl kt) (n :: Nat) where
  rdict_2 :: Proxy# c -> Proxy# p -> Proxy# n -> SV n Any

instance RAll2 c ('NRow0 :: NRow kl kt) 0 where
  {-# INLINE rdict_2 #-}
  rdict_2 _ _ _ = V0

$(concat <$> mapM rAllTH [1..16])

------------------------------

-- | A variant type.
data V (f :: kl -> kt -> *) (p :: Row kl kt) = MkV !Any !Word16

instance RAll (ShowCol f) p => Show (V f (p :: Row kl kt)) where
  {-# INLINE showsPrec #-}
  showsPrec _d v = case vproof v of HasSomeCol{} -> showChar '<' . velim (table /$\ rdictCol proxy#) v . showChar '>'
    where
    table :: forall l t. (D (ShowCol f) :->: f :->: C ShowS) l t
    {-# INLINE table #-}
    table = A $ \Dict -> A $ \flt -> C $
      showsColName (proxy# :: Proxy# l) . showChar ' ' . showsPrec appPrec1 flt

-- | A variant is itself proof that the row is non-empty.
vproof :: forall f (p :: Row kl kt). V f p -> HasSomeCol p
{-# INLINE vproof #-}
vproof MkV{} = unsafeCoerce (Refl :: () :~: ())

-- | Inject a value into a variant.
mkV :: forall f (p :: Row kl kt) l t. Lacks p l => f l t -> V f (p .& l .= t)
{-# INLINE mkV #-}
mkV = \flt -> MkV (unsafeCoerce flt) $ toEnum $ fromEnum $ rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)

-- | Make a singleton invariant.
vone :: f l t -> V f (Row0 .& l .= t :: Row kl kt)
{-# INLINE vone #-}
vone = \flt -> MkV (unsafeCoerce flt) 0

infixl 1 .+ , .- , .-+

-- | Weaken a variant.
(.+) :: forall f (p :: Row kl kt) proxy l t. Lacks p l => V f p -> proxy l -> V f (p .& l .= t)
{-# INLINE (.+) #-}
(.+) = \(MkV flt w) _ -> MkV flt $ let
  o = toEnum (fromEnum (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)))
  in
  if w >= o
  then w+1
  else w

-- | Eliminate a void variant.
vabsurd :: V f (Row0 :: Row kl kt) -> a
{-# INLINE vabsurd #-}
vabsurd = error "empty variant"

-- | Eliminate a singleton variant.
vsingleton :: V f (Row0 .& l .= t :: Row kl kt) -> f l t
{-# INLINE vsingleton #-}
vsingleton (MkV flt _) = unsafeCoerce flt

-- | Eliminate a homogenous variant.
vconstant :: V (C a) p -> a
{-# INLINE vconstant #-}
vconstant (MkV flt _) = unsafeCoerce flt

-- | Strengthen a variant.
(.-) :: forall f (p :: Row kl kt) proxy l t. Lacks p l => V f (p .& l .= t) -> proxy l -> Either (V f p) (f l t)
{-# INLINE (.-) #-}
(.-) = \(MkV flt w) _ -> let
  o = toEnum (fromEnum (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)))
  in case compare w o of
  LT -> Left $ MkV flt w
  EQ -> Right (unsafeCoerce flt)
  GT -> Left $ MkV flt (w-1)

-- | Update a variant.
(.-+) :: forall f (p :: Row kl kt) l t1 t2. Lacks p l => V f (p .& l .= t1) -> f l t2 -> V f (p .& l .= t2)
{-# INLINE (.-+) #-}
(.-+) = \(MkV flt1 w) flt2 -> let
  o = toEnum (fromEnum (rowInsertionOffset (proxy# :: Proxy# p) (proxy# :: Proxy# l)))
  in flip MkV w $ case compare w o of
  LT -> flt1
  EQ -> unsafeCoerce flt2
  GT -> flt1

------------------------------

-- | Apply a functional record to an argument. (Gaster and Jones
-- 1996)
--
-- @introR r a = r /*\ rpure (C a)@
rintro :: Short (NumCols p) => R (C a :->: f) p -> a -> R f p
{-# INLINE rintro #-}
rintro (MkR sv) a = MkR $ fmap (unsafeCoerce ($ C a)) sv

-- | Apply a functional variant to an argument. (Gaster and Jones
-- 1996)
vintro :: V (C a :->: f) p -> a -> V f p
{-# INLINE vintro #-}
vintro (MkV flt w) a = MkV (unsafeCoerce unA flt (C a)) w

-- | Eliminate a variant with a functional record. (Gaster and Jones
-- 1996)
--
-- @vconstant  = velim . rpure (A id)@
velim :: Short (NumCols p - 1) => R (f :->: C a) p -> V f p -> a
{-# INLINE velim #-}
velim (MkR sv) v@(MkV flt w) = case vproof v of HasSomeCol{} -> unC $ unsafeCoerce unA (select sv w) flt

-- | Eliminate a record with a functional variant. (Gaster and Jones
-- 1996)
relim :: Short (NumCols p - 1) => V (f :->: C a) p -> R f p -> a
{-# INLINE relim #-}
relim v@(MkV flt w) (MkR sv) = case vproof v of HasSomeCol{} -> unC $ unsafeCoerce unA flt (select sv w)

-- | Convert each field to a variant of the same row.
rvariants :: forall (p :: Row kl kt) f. Short (NumCols p) => R f p -> R (C (V f p)) p
{-# INLINE rvariants #-}
rvariants r = f /$\ rhas /*\ r
  where
  f :: forall (l :: kl) (t :: kt). (HasCol p :->: f :->: C (V f p)) l t
  {-# INLINE f #-}
  f = A $ \HasCol -> A $ \x -> C $ mkV x

-- | Partition a list of variants into in list-shaped record of the
-- same row.
vpartition :: forall (p :: Row kl *) f. (Foldable f,Short (NumCols p),Short (NumCols p - 1)) => f (V I p) -> R (F []) p
{-# INLINE vpartition #-}
vpartition = foldr cons (rpure (F []))
  where
  {-# INLINE cons #-}
  cons v !acc = velim (f /$\ rhas) v
    where
    f :: forall (l :: kl) t. (HasCol p :->: I :->: C (R (F []) p)) l t
    {-# INLINE f #-}
    f = A $ \HasCol -> A $ \x -> C $ runIdentity $ rlens (Identity . g x) acc

  g :: forall (l :: kl) t. I l t -> F [] l t -> F [] l t
  {-# INLINE g #-}
  g (I x) (F xs) = F (x:xs)

-----

instance GenericNR f (Normalize p) (NumCols p) => G.Generic (R f (p :: Row kl kt)) where
  type Rep (R f p) = RepNR f (Normalize p) (NumCols p)
  {-# INLINE from #-}
  from (MkR sv) = fromNR (proxy# :: Proxy# f) (proxy# :: Proxy# (Normalize p)) (proxy# :: Proxy# (NumCols p)) sv
  {-# INLINE to #-}
  to = MkR . toNR (proxy# :: Proxy# f) (proxy# :: Proxy# (Normalize p)) (proxy# :: Proxy# (NumCols p))

class GenericNR (f :: kl -> kt -> *) (p :: NRow kl kt) (n :: Nat) where
  type family RepNR f p n :: * -> *
  fromNR :: Proxy# f -> Proxy# p -> Proxy# n -> SV n Any -> RepNR f p n x
  toNR :: Proxy# f -> Proxy# p -> Proxy# n -> RepNR f p n x -> SV n Any

type GDR s c = G.D1 ('G.MetaData s "Data.Sculls.Record" "sculls" 'False) c
type GCR (s :: Symbol) fs = G.C1 ('G.MetaCons s 'G.PrefixI 'False) fs
type GSR (l :: kl) = 'G.MetaSel
  ('Just (ColSymbol l))
  'G.NoSourceUnpackedness
  'G.SourceStrict
  'G.DecidedStrict
type SGR f l t = G.S1 (GSR l) (G.Rec0 (f l t))
sgr :: Any -> SGR f l t x
sgr = unsafeCoerce

-----

instance GenericNV f (Normalize p) (NumCols p) => G.Generic (V f (p :: Row kl kt)) where
  type Rep (V f p) = RepNV f (Normalize p) (NumCols p)
  {-# INLINE from #-}
  from (MkV flt w) = fromNV (proxy# :: Proxy# f) (proxy# :: Proxy# (Normalize p)) (proxy# :: Proxy# (NumCols p)) flt w
  {-# INLINE to #-}
  to = toNV (proxy# :: Proxy# f) (proxy# :: Proxy# (Normalize p)) (proxy# :: Proxy# (NumCols p)) MkV

class GenericNV (f :: kl -> kt -> *) (p :: NRow kl kt) (n :: Nat) where
  type family RepNV f p n :: * -> *
  fromNV :: Proxy# f -> Proxy# p -> Proxy# n -> Any -> Word16 -> RepNV f p n x
  toNV :: Proxy# f -> Proxy# p -> Proxy# n -> (Any -> Word16 -> r) -> RepNV f p n x -> r

type GDV s c = G.D1 ('G.MetaData s "Data.Sculls.Variant" "sculls" 'False) c
type GCV (s :: Symbol) fs = G.C1 ('G.MetaCons s 'G.PrefixI 'False) fs
type GSV (l :: kl) = 'G.MetaSel
  'Nothing
  'G.NoSourceUnpackedness
  'G.SourceStrict
  'G.DecidedStrict
type SGV f l t = G.S1 (GSV l) (G.Rec0 (f l t))
sgv :: Any -> SGV f l t x
sgv = unsafeCoerce

-----

$(concat <$> mapM genericsTH [0..17])
