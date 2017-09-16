-- | This module rexports (almost) every part of the GHC API that the
-- plugin uses.

module GHCAPI (
  Class,
  Ct(..),
  CtEvidence(..),
  DataCon,
  EqRel(..),
  EvLit(..),
  EvTerm(..),
  Kind,
  Outputable(..),
  PredTree(..),
  PredType,
  TCvSubst,
  TcPlugin(..),
  TcPluginResult(..),
  TcPluginM,
  TcTyVar,
  TyCon,
  TyVar,
  Type(..),
  anyTyCon,
  classifyPredType,
  classTyCon,
  composeTCvSubst,
  constraintKind,
  ctEvidence,
  ctEvPred,
  ctEvTerm,
  ctLoc,
  ctPred,
  emptyTCvSubst,
  eqTyConName,
  eqType,
  TcType.extendTvSubst,
  fsLit,
  getTcLevel,
  getTyVar_maybe,
  instanceDFunId,
  isCDictCan_Maybe,
  isCFunEqCan,
  isCTyEqCan,
  isDerivedCt,
  isEmptyTCvSubst,
  isFlattenTyVar,
  isNumLitTy,
  isTouchableTcPluginM,
  mkNonCanonical,
  mkNumLitTy,
  mkPrimEqPred,
  mkTyConApp,
  mkTyConTy,
  mkTyVarOccFS,
  mkTyVarTy,
  nameOccName,
  newDerived,
  newFlexiTyVar,
  newGiven,
  newWanted,
  occNameFS,
  panic,
  promoteDataCon,
  setTyVarName,
  splitTyConApp_maybe,
  TcType.substTy,
  tcLookupTyCon,
  tcPluginIO,
  tcTyVarDetails,
  tidyNameOcc,
  tyCoVarsOfType,
  tyCoVarsOfTypeList,
  tyVarKind,
  typeKind,
  unsafeTcPluginTcM,
  varName,
  varUnique,
  zonkCt,
  zonkTcType,
  module UniqFM,
  module UniqSet,
  module VarSet,
  ) where

import Class
import GhcPlugins
import InstEnv
import PrelNames
import TcEvidence
import TcPluginM
import TcRnMonad
import TyCoRep
import TcType (TcTyVar,extendTvSubst,isFlattenTyVar,substTy)
import UniqFM
import UniqSet
import VarSet
