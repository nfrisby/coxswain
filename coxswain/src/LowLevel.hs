{-# LANGUAGE LambdaCase #-}

-- | This module defines some low-level API-like functions: debug
-- logging, "Coxswain" module inspections, fresh variable generation
-- (more specialized than 'newFlexiTyVar'), and --- most notably ---
-- the deterministic partial type comparison function 'detCmpType'.

module LowLevel (
  coxClass,
  coxDataCon,
  coxTyCon,
  coxFiatCo,
  detCmpType,
  dumpSummarize,
  dumpSummarize_,
  dumpSummarize__,
  dumpSummarizeMany,
  dumpTrace,
  dumpTrace_,
  dumpTrace__,
  dumpTraceMany,
  dump__,
  dumpMany_,
  dumpFlush,
  lookupSoleClsInst,
  refreezeTyVar,
  thawTyVar,
  ) where

import qualified E
import GHCAPI

import Control.Applicative (liftA2)
import Control.Monad (when)
import System.IO (Handle,hFlush,hPutStrLn,stderr)

import GHC.Fingerprint
import GhcPlugins
import qualified HscTypes as D (hsc_dflags)
import InstEnv
import qualified Outputable as D
import Panic
import qualified TcPluginM as D (getTopEnv,tcPluginIO)
import TyCoRep
import TcPluginM
import TcRnMonad (newMutVar)
import TcType (MetaDetails(..),MetaInfo(..),TcTyVarDetails(..),tcTyVarLevel)

coxswainPkg :: FastString
coxswainPkg = fsLit "coxswain"

coxswainMod :: ModuleName
coxswainMod = mkModuleName "Coxswain"

coxClass :: String -> TcPluginM Class
coxClass nm = coxName (mkClsOcc nm) >>= tcLookupClass

coxDataCon :: String -> TcPluginM DataCon
coxDataCon nm = coxName (mkDataOcc nm) >>= tcLookupDataCon

coxModule :: TcPluginM Module
coxModule = do
  found_module <- findImportedModule coxswainMod (Just coxswainPkg)
  case found_module of
    Found _ h -> return h
    _ -> do
      found_module' <- findImportedModule coxswainMod $ Just (fsLit "this")
      case found_module' of
        Found _ h -> return h
        _ -> panicDoc "Unable to resolve module looked up by plugin: " (ppr coxswainMod)

coxName :: OccName -> TcPluginM Name
coxName occ = coxModule >>= \md -> lookupOrig md occ

coxTyCon :: String -> TcPluginM TyCon
coxTyCon nm = coxName (mkTcOcc nm) >>= tcLookupTyCon

-----

lookupSoleClsInst :: Class -> TcPluginM ClsInst
lookupSoleClsInst cls = do
  instEnvs <- getInstEnvs
  case classInstances instEnvs cls of
    [inst] -> return inst
    _ -> panic "Did not find exactly one instance looked up by plugin: " (ppr cls)

-----

coxFiatCo :: Type -> Type -> Coercion
coxFiatCo = mkUnivCo (PluginProv "coxswain") Nominal

-----

detCmpType :: Type -> Type -> Maybe Ordering
detCmpType = detCmpTypeX (mkRnEnv2 emptyInScopeSet)

data E = E {-# UNPACK #-} !Int !(VarEnv Int) !RnEnv2

eRnEnv2 :: E -> RnEnv2
eRnEnv2 (E _ _ re) = re

emptyE :: RnEnv2 -> E
emptyE = E 0 emptyVarEnv

lookupE :: E -> Var -> Maybe Int
lookupE (E _ ve _) v = lookupVarEnv ve v

bndrE :: E -> Var -> Var -> E
bndrE (E i ve re) v1 v2 = E (i+1) (extendVarEnv ve v i) re'
  where
  (re',v) = rnBndr2_var re v1 v2

-- An adaptation of Type.nonDetCmpTypeX to be deterministic.
detCmpTypeX :: RnEnv2 -> Type -> Type -> Maybe Ordering
detCmpTypeX = go . emptyE
  where
    liftOrdering :: Ordering -> Maybe Ordering
    liftOrdering = Just

    thenCmpTy :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
    thenCmpTy = liftA2 f
      where
      f EQ rel = rel
      f rel _ = rel

    giveUpUnlessEqual :: Maybe Ordering -> Maybe Ordering
    giveUpUnlessEqual = \case
      Just EQ -> Just EQ
      _ -> Nothing

    go :: E -> Type -> Type -> Maybe Ordering
    go env t1 t2
      | Just t1' <- coreView t1 = go env t1' t2
      | Just t2' <- coreView t2 = go env t1 t2'

    go env (TyVarTy tv1) (TyVarTy tv2)
      | tv1 == tv2 = liftOrdering EQ
      | otherwise =
          compare  -- de Bruijn indices
      <$> (rnOccL_maybe (eRnEnv2 env) tv1 >>= lookupE env)
      <*> (rnOccR_maybe (eRnEnv2 env) tv2 >>= lookupE env)
    go env (ForAllTy (TvBndr tv1 _) t1) (ForAllTy (TvBndr tv2 _) t2)
      = go env (tyVarKind tv1) (tyVarKind tv2)
        `thenCmpTy` go (bndrE env tv1 tv2) t1 t2
    go env (AppTy s1 t1) ty2
      | Just (s2, t2) <- repSplitAppTy_maybe ty2
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env ty1 (AppTy s2 t2)
      | Just (s1, t1) <- repSplitAppTy_maybe ty1
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env (FunTy s1 t1) (FunTy s2 t2)
      = go env s1 s2 `thenCmpTy` go env t1 t2
    go env (TyConApp tc1 tys1) (TyConApp tc2 tys2)
      = (if isFamilyTyCon tc1 || isFamilyTyCon tc2 then giveUpUnlessEqual else id)   -- TODO Use 'FamInstEnv.apartnessCheck'
      $ liftOrdering (tc1 `detCmpTc` tc2) `thenCmpTy` gos env tys1 tys2
    go _   (LitTy l1)          (LitTy l2)          = liftOrdering (compare l1 l2)
    go env (CastTy t1 _)       t2                  = go env t1 t2
    go env t1                  (CastTy t2 _)       = go env t1 t2

    go _   (CoercionTy {})     (CoercionTy {})     = liftOrdering EQ

    go env (TyVarTy tv) _ | Nothing <- lookupE env tv = Nothing   -- free tyvars might match later
    go env _ (TyVarTy tv) | Nothing <- lookupE env tv = Nothing   -- free tyvars might match later

    go _ ty1 ty2
      = liftOrdering $ (get_rank ty1) `compare` (get_rank ty2)
      where get_rank :: Type -> Int
            get_rank (CastTy {})
              = pprPanic "Coxswain.GHCAPI.detCmpType.get_rank" (ppr [ty1,ty2])
            get_rank (TyVarTy {})    = 0
            get_rank (CoercionTy {}) = 1
            get_rank (AppTy {})      = 3
            get_rank (LitTy {})      = 4
            get_rank (TyConApp {})   = 5
            get_rank (FunTy {})      = 6
            get_rank (ForAllTy {})   = 7

    gos :: E -> [Type] -> [Type] -> Maybe Ordering
    gos _   []         []         = liftOrdering EQ
    gos _   []         _          = liftOrdering LT
    gos _   _          []         = liftOrdering GT
    gos env (ty1:tys1) (ty2:tys2) = go env ty1 ty2 `thenCmpTy` gos env tys1 tys2

detCmpTc :: TyCon -> TyCon -> Ordering
detCmpTc tc1 tc2 = mkTyConFingerprint tc1 `compare` mkTyConFingerprint tc2

mkTyConFingerprint :: TyCon -> Fingerprint
mkTyConFingerprint tc =
  fingerprintFingerprints
  [ fingerprintString (moduleStableString modu)
  , fingerprintString (getOccString nm)
  ]
  where
  nm = tyConName tc
  modu = nameModule nm

-----

dumpSummarize :: Outputable a => E.E -> String -> a -> TcPluginM a
dumpSummarize e s a = a <$ dumpSummarize_ e s (ppr a)

dumpSummarize_ :: E.E -> String -> D.SDoc -> TcPluginM ()
dumpSummarize_ e s x = when (E.cloSummarize e) $ dump__ e (D.text s D.<+> x)

dumpSummarize__ :: E.E -> D.SDoc -> TcPluginM ()
dumpSummarize__ e x = when (E.cloSummarize e) $ dump__ e x

dumpTrace :: Outputable a => E.E -> String -> a -> TcPluginM a
dumpTrace e s a = a <$ dumpTrace_ e s (ppr a)

dumpTrace_ :: E.E -> String -> D.SDoc -> TcPluginM ()
dumpTrace_ e s x = when (E.cloTrace e) $ dump__ e (D.text s D.<+> x)

dumpTrace__ :: E.E -> D.SDoc -> TcPluginM ()
dumpTrace__ e x = when (E.cloTrace e) $ dump__ e x

dumpSummarizeMany :: Outputable a => E.E -> String -> [a] -> TcPluginM ()
dumpSummarizeMany e s xs = when (E.cloSummarize e) $ dumpMany_ e s (map D.ppr xs)

dumpTraceMany :: Outputable a => E.E -> String -> [a] -> TcPluginM ()
dumpTraceMany e s xs = when (E.cloTrace e) $ dumpMany_ e s (map D.ppr xs)

dumpMany_ :: E.E -> String -> [D.SDoc] -> TcPluginM ()
dumpMany_ e s ds = dump__ e $ D.text s D.$+$ D.nest 2 (foldr (D.$+$) D.empty ds)

dump__ :: E.E -> D.SDoc -> TcPluginM ()
dump__ e x = when (E.cloDebug e) $ do
  dflags <- D.hsc_dflags <$> D.getTopEnv
  D.tcPluginIO $ hPutStrLn (dumpHandle e) $ D.showSDocDump dflags x

dumpFlush :: E.E -> TcPluginM ()
dumpFlush e = when (E.cloDebug e) $ D.tcPluginIO $ hFlush (dumpHandle e)

dumpHandle :: E.E -> Handle
dumpHandle e = case E.cloLogFile e of
  Nothing -> stderr
  Just h -> h

-----

-- | Create a unification variable with the same kind and level.
thawTyVar :: TcTyVar -> TcPluginM TcTyVar
thawTyVar tv = do
  uq <- newUnique
  let name = mkSysTvName uq (fsLit "$coxswainTau")
  ref <- unsafeTcPluginTcM (newMutVar Flexi)
  let details = MetaTv{mtv_info = TauTv,mtv_ref = ref,mtv_tclvl = tcTyVarLevel tv}
  return (mkTcTyVar name (varType tv) details)

-- | Create a skolem variable with the same kind and level.
refreezeTyVar :: TcTyVar -> TcPluginM TcTyVar
refreezeTyVar tv = do
  uq <- newUnique
  let name = mkSysTvName uq (fsLit "$coxswainSko")
  return (mkTcTyVar name (varType tv) (SkolemTv (tcTyVarLevel tv) False))
