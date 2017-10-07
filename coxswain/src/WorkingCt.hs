{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

-- | The 'working' function builds a plugin from functions for three
-- phases: activation, simplification, and deactivation.

module WorkingCt (GW(..),working) where

import Data.Foldable (foldMap)
import Data.IORef
import Data.Monoid

import E
import GHCAPI
import LowLevel
import Simplify
import ZonkGivens

import qualified Outputable as D
import TcRnTypes (TcEvDest(..))

-- | For generalizing over simplifying givens and solving wanteds.
data GW :: * -> * where
  G :: GW [Ct]
  W :: GW ([Ct],[Ct],[Ct])

instance Show (GW gw) where
  show = \case
    G -> "G"
    W -> "W"

solveGW :: GW gw -> Ct -> (EvTerm,Ct)
solveGW G ct = (ctEvTerm (ctEvidence ct),ct)
solveGW W ct = (EvDelayedError (ctPred ct) (fsLit "Coxswain: solveGW"),ct)

newGW :: GW gw -> gw -> Type -> TcPluginM Ct
newGW G gs t = do
  let ct0 = head gs
  let ev = coxFiatCast (ctPred ct0) t (ctEvTerm (ctEvidence ct0))
  mkNonCanonical <$> newGiven (ctLoc ct0) t ev
newGW W (_,_,ws) t = mkNonCanonical <$> newWanted (ctLoc (head ws)) t

dumpStartGW :: E -> GW gw -> gw -> TcPluginM ()
dumpStartGW e gw cts = case (gw,cts) of
  (G,gs) -> do
    dumpHeader
    dumpSummarizeMany e ("activating " ++ show gw) $ map snd $ filter (not . isCFunEqCan . fst) $ zonkGivens gs
    dumpFlush e
  (W,(gs,ds,ws)) -> do
    dumpHeader
    dumpSummarize_ e "activating" (D.text (show gw))
    dumpSummarizeMany e "given" $ map snd $ filter (not . isCFunEqCan . fst) $ zonkGivens gs
    dumpSummarizeMany e "derived" ds
    dumpSummarizeMany e "wanted" ws
    dumpFlush e
  where
  dumpHeader = do
    c <- tcPluginIO $ do
      let cntr = taskCounter e
      c <- readIORef cntr
      writeIORef cntr (c+1)
      return (c+1)
    d <- tcPluginIO $ readIORef $ invocationCounter e
    dumpSummarize__ e $ D.text $ "----- " ++ show (c,d) ++ " ------"


dumpDoneGW :: E -> Maybe Ct -> GW gw -> gw -> TcPluginM ()
dumpDoneGW e mb_ct gw cts = case (gw,cts) of
  (G,gs) -> do
    let gs2 = maybe id (\ct -> filter (not . sameCt ct)) mb_ct gs
    dumpSummarizeMany e ("done " ++ show gw) $ map snd $ filter (not . isCFunEqCan . fst) $ zonkGivens gs2
    dumpFlush e
  (W,(_,_,ws)) -> do
    let ws2 = maybe id (\ct -> filter (not . sameCt ct)) mb_ct ws
    dumpSummarizeMany e ("done " ++ show gw) ws2
    dumpFlush e

-----

data PhaseResult =
    Activated SolvedNew
    -- ^ The first phase is to "activate". For coxswain's simplifying
    -- givens, this is the thawing substitution, for example.
  |
    Simplified TcPluginResult
    -- ^ The second phase is to actually simplify.
  |
    Deactivated SolvedNew
    -- ^ The third phase is to "deactivate." For coxswain's
    -- simplifying givens, this is the refreezing substitution, for
    -- example.
  |
    Stop

-- | Analyze the existing constraints to determine what phase we're in
-- for this invocation.
alreadyWorking :: GW gw -> E -> gw -> Maybe (Ct,Integer)
alreadyWorking gw e cts0 = getFirst $ foldMap (First . f) cts1
  where
  f ct = case splitTyConApp_maybe (ctPred ct) of
    Just (hed,[arg])
      | hed == classTyCon (workingClass e)
      , Just phase <- isNumLitTy arg
      -> Just (ct,phase)
    _ -> Nothing

  cts1 :: [Ct]
  cts1 = case (gw,cts0) of
    (G,gs) -> gs
    (W,(_,_,ws)) -> ws

-- | Implements a plugin according to the phases overview in the
-- 'PhaseResult' Haddock.
working ::
     GW gw
  -> (E -> gw -> TcPluginM SolvedNew)
  -> (E -> gw -> TcPluginM TcPluginResult)
  -> Maybe (E -> gw -> TcPluginM SolvedNew)
  -> E
  -> gw
  -> TcPluginM TcPluginResult
working gw activate simplify mb_deactivate e cts = go False (snd <$> state0)
  where
  state0 = alreadyWorking gw e cts

  go :: Bool -> Maybe Integer -> TcPluginM TcPluginResult
  go recurred phase = runThisPhase phase >>= \case
    Activated sn
      | MkSolvedNew [] [] <- sn -> recur
      | otherwise -> advanceThePhase sn

    Simplified r@TcPluginContradiction{} -> return r
    Simplified (TcPluginOk solved new)
      | not (null new) -> continueThisPhase sn
      | otherwise -> case mb_deactivate of
        Nothing -> stop sn
        Just _ -> if null solved then recur else advanceThePhase sn
      where
      sn = MkSolvedNew solved new

    -- If deactivation creates new constraints, then GHC will invoke
    -- the plugin again. So we need to add in a new working
    -- constraint, otherwise the next invocation will start over from
    -- the initial state!
    Deactivated sn
      | MkSolvedNew _ [] <- sn -> stop sn
      | otherwise -> advanceThePhase sn

    Stop -> stop mempty
    where
    advanceThePhase sn = generateNew nextPhase (discardOld sn)
    continueThisPhase = (if recurred then generateNew (nextPhase - 1) else return) . success   -- INVARIANT: recurred implies nextPhase > 1
    recur = go True (Just nextPhase)
    stop sn = do
      debugMessage "done"
      dumpDoneGW e (fst <$> state0) gw cts
      return (discardOld sn)

    nextPhase = case phase of
      Nothing -> 0
      Just i -> i+1

    discardOld sn@(MkSolvedNew solved new) = case fst <$> state0 of
      Nothing -> success sn
      Just ct -> TcPluginOk (solveGW gw ct : solved) new

    generateNew ph = \case
      r@TcPluginContradiction{} -> return r
      TcPluginOk solved new -> do
        ct <- newGW gw cts $ classTyCon (workingClass e) `mkTyConApp` [mkNumLitTy ph]
        return (TcPluginOk solved (ct : new))

  runThisPhase :: Maybe Integer -> TcPluginM PhaseResult
  runThisPhase = \case
    Nothing -> do
      debugMessage "activating"
      dumpStartGW e gw cts
      Activated <$> activate e cts

    Just 0 -> do
      debugMessage "simplifying"
      Simplified <$> simplify e cts

    Just 1
      | Just deactivate <- mb_deactivate -> do
      debugMessage "deactivating"
      Deactivated <$> deactivate e cts

    -- This is either 1 or 2, depending on if there's a deactivation
    -- phase.
    Just _ -> return Stop

  debugMessage s = dumpTrace_ e s (D.text (show gw))

sameCt :: Ct -> Ct -> Bool
sameCt ct1 ct2 = go (ctEvidence ct1) (ctEvidence ct2)
  where
  go CtGiven{ctev_evar=ev1} CtGiven{ctev_evar=ev2} = ev1 == ev2
  go CtWanted{ctev_dest=EvVarDest ev1} CtWanted{ctev_dest=EvVarDest ev2} = ev1 == ev2
  go _ _ = False
