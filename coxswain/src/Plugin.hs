{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

module Plugin (
  plugin,
  ) where

import Control.Arrow (first,second)
import Control.Monad (foldM)
import Data.IORef
import System.IO

import E (E(..))
import GHCAPI
import LowLevel
import SimplifyGivens (simplifyGivens)
import SimplifyWanteds (simplifyWanteds)
import ZonkGivens (zonkGivens)

import qualified Outputable as D
import Plugins (Plugin(..),defaultPlugin)

-- | The @coxswain@ typechecker plugin.
--
-- Activate it by supplying @-fplugin=Coxswain@ to @ghc@. For
-- non-trivial programs, you may also need
-- @-fconstraint-solver-iterations=0@ (or some large @N@).
plugin :: Plugin
plugin = defaultPlugin { tcPlugin = \args -> Just (coxswainPlugin args) }

coxswainPlugin :: [String] -> TcPlugin
coxswainPlugin clos = TcPlugin {
    tcPluginInit = initialize clos
  ,
    tcPluginSolve = k
  ,
    tcPluginStop  = finalize
  }
  where
  -- We operate in two distinct modes, indicated by the absence or
  -- presence of wanteds.
  k e given derived wanted
    | not (null wanted) = do
      dumpHeader
      dumpCts "given" given
      dumpCts "zonk given" $ map snd $ filter (not . isCFunEqCan . fst) $ zonkGivens given
      dumpCts "derived" derived
      dumpCts "wanted" wanted
      dumpVars
      dumpFlush e
      simplifyWanteds e given derived wanted >>= dumpResult
    | otherwise = do
      dumpHeader
      dumpCts "given only" given
      dumpCts "zonk given only" $ map snd $ filter (not . isCFunEqCan . fst) $ zonkGivens given
      dumpVars
      dumpFlush e
      simplifyGivens e given >>= dumpResult
    where
    dumpHeader = do
      d <- tcPluginIO $ do
        let cntr = invocationCounter e
        d <- readIORef cntr
        writeIORef cntr (d+1)
        return (d+1)
      dumpTrace__ e $ D.text $ "----- " ++ show d ++ " ------"

    dumpCts s = dumpTraceMany e s

    -- Partition touchable and untouchable variables.
    dumpVars = do
      let cts = given ++ derived ++ wanted
      let vars = nonDetEltsUniqSet $ unionVarSets $ map (tyCoVarsOfType . ctEvPred . ctEvidence) cts
      (touchables,untouchables) <- foldM (\acc a -> isTouchableTcPluginM a >>= \b -> return $ (if b then first else second) (a:) acc) ([],[]) vars
      _ <- dumpTrace e "untouchables" untouchables
      _ <- mapM (\tv -> (,) tv <$> zonkTcType (mkTyVarTy tv)) touchables >>= dumpTraceMany e "touchables"
      return ()

    dumpResult x = do
      _ <- case x of
        TcPluginContradiction contras -> dumpTraceMany e "contradictions" contras
        TcPluginOk solved new -> dumpTraceMany e "solved" (map snd solved) >> dumpTraceMany e "new" new
      dumpFlush e
      return x

-----

-- | Lookup the "Coxswain" declarations that we treat specially, parse options,
-- initialize counters, and so on.
initialize :: [String] -> TcPluginM E
initialize clos = do
  let cloRefreeze = not $ any (== "no-refreeze") clos
  let cloSummarize0 = any (== "summarize") clos
  let cloTrace = any (== "trace") clos
  let cloThaw = not $ any (== "no-thaw") clos

  let cloSummarize = cloSummarize0 && not cloTrace
  let cloDebug = cloSummarize || cloTrace

  colTC <- coxTyCon "Col"
  cloLogFile <- case [ f | 'l':'o':'g':'f':'i':'l':'e':'=':f <- clos ] of
    _ | not cloDebug -> return Nothing
    [f] -> tcPluginIO $ Just <$> openFile f WriteMode
    [] -> return Nothing
    _:_ -> error "multiple logfile options for Coxswain plugin"
  emptyTC <- coxTyCon "Row0"
  eqTwiddleTC <- tcLookupTyCon eqTyConName
  extTC <- coxTyCon ".&"
  plusLacksDFunId <- fmap instanceDFunId $ coxClass "Lacks_Plus" >>= lookupSoleClsInst
  invocationCounter <- tcPluginIO (newIORef 0)
  knownNat16Cls <- coxClass "KnownNat16"
  lacksCls <- coxClass "Lacks"
  minusLacksDFunId <- fmap instanceDFunId $ coxClass "Lacks_Minus" >>= lookupSoleClsInst
  mkColTC <- coxTyCon ".="
  nextTC <- promoteDataCon <$> coxDataCon "NExt"
  normTC <- coxTyCon "Normalize"
  nrowTC <- promoteDataCon <$> coxDataCon "NRow0"
  numColsTC <- coxTyCon "NumCols"
  renClass <- coxClass "Ren"
  restrictionTC <- coxTyCon "Restriction"
  rowTC <- coxTyCon "Row"
  taskCounter <- tcPluginIO (newIORef 0)
  times2Cls <- coxClass "Times2"
  times2DFunId <- fmap instanceDFunId $ lookupSoleClsInst times2Cls
  times2Plus1Cls <- coxClass "Times2Plus1"
  times2Plus1DFunId <- fmap instanceDFunId $ lookupSoleClsInst times2Plus1Cls
  workingClass <- coxClass "CoxswainWorking"
  zeroLacksDFunId <- fmap instanceDFunId $ coxClass "Lacks_Zero" >>= lookupSoleClsInst
  zeroCls <- coxClass "Zero"
  zeroDFunId <- fmap instanceDFunId $ lookupSoleClsInst zeroCls

  let e = MkE{colTC,cloDebug,cloLogFile,cloRefreeze,cloSummarize,cloThaw,cloTrace,emptyTC,eqTwiddleTC,extTC,invocationCounter,knownNat16Cls,lacksCls,minusLacksDFunId,mkColTC,nextTC,normTC,nrowTC,numColsTC,plusLacksDFunId,renClass,restrictionTC,rowTC,taskCounter,times2Cls,times2DFunId,times2Plus1Cls,times2Plus1DFunId,workingClass,zeroCls,zeroDFunId,zeroLacksDFunId}

  dumpMany_ e "plugin arguments" (map D.text clos)

  return e

-- | The logfile is the only finalizable resource we have.
finalize :: E -> TcPluginM ()
finalize e = case cloLogFile e of
  Nothing -> return ()
  Just h -> tcPluginIO (hClose h)
