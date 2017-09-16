-- Some basic snippets from the sculls library.

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=6 #-}

import Coxswain
import Data.Proxy (Proxy(Proxy))
import GHC.TypeLits
import Unsafe.Coerce (unsafeCoerce)

data R (f :: kl -> kt -> *) (p :: Row kl kt) = MkR

sel :: forall f p (l :: kl) (t :: kt). (Lacks p l) => R f (p .& l .= t) -> f l t
sel MkR = undefined

infixl 1 .* , ./

(.*) :: forall f p (l :: kl) (t :: kt). (Lacks p l) => R f p -> f l t -> R f (p .& l .= t)
(.*) = \MkR _ -> MkR

(./) :: forall f p (l :: kl) (t :: kt) proxy. (Lacks p l) => R f (p .& l .= t) -> proxy l -> R f p
(./) = \MkR _ -> MkR

_lens :: forall f p (l :: kl) (t1 :: kt) t2. (Lacks p l) => (f l t1 -> f l t2) -> R f (p .& l .= t1) -> R f (p .& l .= t2)
_lens = \f r -> (\x -> r ./ (Proxy :: Proxy l) .* unsafeCoerce (x :: f l t2)) $ (unsafeCoerce (sel r :: f l t1))
