-- Exercising local assumptions with a snippet from the sculls
-- library.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

import Coxswain
import Data.Type.Equality

data Has :: Row kl kt -> Row kl kt -> kl -> kt -> * where
  Has :: Has (q .& l .= t) q l t

mkHas :: p :~: (q .& l .= t) -> Has p q l t
mkHas Refl = Has
