module E where

import Data.IORef (IORef)
import System.IO (Handle)

import GHC
import Var (DFunId)

-- | The private environment and state of the plugin.
--
-- All of the type constructors, classes, dictionariy IDs, etc are
-- looked up from the "Coxswain" module by "Plugin"@.initialize@.
data E = MkE {
    colTC :: !TyCon
  ,
    cloDebug :: !Bool
    -- ^ @= cloSummarize || cloTrace@.
  ,
    cloLogFile :: !(Maybe Handle)
    -- ^ Was the @logfile=...@ option present?
  ,
    cloRefreeze :: !Bool
    -- ^ Was the @no-refreeze@ option absent?
  ,
    cloSummarize :: !Bool
    -- ^ Was the @summarize@ option present?
  ,
    cloThaw :: !Bool
    -- ^ Was the @no-thaw@ option absent?
  ,
    cloTrace :: !Bool
    -- ^ Was the @trace@ option present?
  ,
    emptyTC :: !TyCon
  ,
    eqTwiddleTC :: TyCon
  ,
    extTC :: !TyCon
  ,
    plusLacksCls :: !Class
  ,
    plusLacksDFunId :: !DFunId
  ,
    invocationCounter :: !(IORef Int)
    -- ^ How many times GHC has invoked the plugin.
  ,
    knownNat16Cls :: !Class
  ,
    lacksCls :: !Class
  ,
    minusLacksCls :: !Class
  ,
    minusLacksDFunId :: !DFunId
  ,
    mkColTC :: !TyCon
  ,
    nextTC :: !TyCon
  ,
    normTC :: !TyCon
  ,
    nrowTC :: !TyCon
  ,
    numColsTC :: !TyCon
  ,
    renClass :: !Class
  ,
    restrictionTC :: !TyCon
  ,
    rowTC :: !TyCon
  ,
    taskCounter :: !(IORef Int)
    -- ^ How many "reasons" GHC has invoked the plugin.
  ,
    times2DFunId :: !DFunId
  ,
    times2Cls :: !Class
  ,
    times2Plus1DFunId :: !DFunId
  ,
    times2Plus1Cls :: !Class
  ,
    workingClass :: !Class
  ,
    zeroCls :: !Class
  ,
    zeroDFunId :: !DFunId
  }
