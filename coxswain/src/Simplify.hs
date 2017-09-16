module Simplify where

import GHCAPI (EvTerm,Ct,TcPluginResult(..))

-- | Result of attempting to simplify something.
--
data Simplification a =
    Contradiction
    -- ^ Found a contradiction.
  |
    Progress !a
    -- ^ Simplified this constraint.
  |
    Yield
    -- ^ *Currently* stuck: can neither learn from nor simplify this
    -- constraint.

-----

-- | The data of 'TcPluginOk'.
data SolvedNew = MkSolvedNew [(EvTerm,Ct)] [Ct]

instance Monoid SolvedNew where
  mempty = MkSolvedNew [] []
  MkSolvedNew l1 l2 `mappend` MkSolvedNew r1 r2 = MkSolvedNew (l1 ++ r1) (l2 ++ r2)

success :: SolvedNew -> TcPluginResult
success (MkSolvedNew solved new) = TcPluginOk solved new
