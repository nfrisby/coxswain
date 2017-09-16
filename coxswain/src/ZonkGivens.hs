{-# LANGUAGE LambdaCase #-}

-- | This module unflattens given constraints by simply building a
-- substitution from the present CFunEqCan constraints (i.e. flatten
-- skolem definitions).
--
-- It's possible 'zonkCt' could replace this, but not absolutely clear
-- to me that is so. In particular --- _perhaps through breaking_
-- _other invariants at the time_ --- I've seen the cached image of
-- flatten skolem be out-of-date with its CFunEqCan's RHS, and that's
-- what 'zonkCt' uses for flatten skolems. That can't happen here.

module ZonkGivens (
  sortGivenBinds,
  substCt,
  zonkGivens,
  ) where

import GHCAPI

import Digraph

-- | A pure function that unflattens flattening skolems.
zonkGivens :: [Ct] -> [(Ct,Ct)]
zonkGivens givens0 =
  [ (ct,substCt sigma ct) | ct <- givens0 ]
  where
  sigma = foldl snoc emptyTCvSubst (sortGivenBinds givens0)
  -- Note: composeTCvSubst applies its first argument to the RHSs of
  -- its second argument.
  snoc acc (v,rhs) = composeTCvSubst (extendTvSubst emptyTCvSubst v rhs) acc

-- | Sort so that the independent variables come last.
sortGivenBinds :: [Ct] -> [(TyVar,Type)]
sortGivenBinds givens0 =
  [ bind | (bind,_,_) <- topologicalSortG (graphFromEdgedVerticesUniq nodes) ]
  where
  funeqs0 = [ (cc_fsk ct,cc_fun ct `mkTyConApp` cc_tyargs ct) | ct@CFunEqCan{} <- givens0 ]

  binds0 = funeqs0
  relevant v = varUnique v `elementOfUniqSet` mkUniqSet (map (varUnique . fst) binds0)
  nodes = [ (bind,v,filter relevant (tyCoVarsOfTypeList rhs)) | bind@(v,rhs) <- binds0 ]

-- | The resulting Ct is ill-formed in a few ways (e.g. flatness of xi
-- types, ill-typed evidence bindings, etc), but it's fine for our
-- local usage: we only care about the types manifest in this data
-- structure.
substCt :: TCvSubst -> Ct -> Ct
substCt sigma = \case
  CDictCan ev c xis pend -> CDictCan (goev ev) c (gos xis) pend
  CIrredEvCan ev -> CIrredEvCan (goev ev)
  CTyEqCan ev _v _rhs _eq -> CNonCanonical (goev ev)
  CFunEqCan ev f xis fsk -> CFunEqCan (goev ev) f (gos xis) fsk
  CNonCanonical ev -> CNonCanonical (goev ev)
  CHoleCan ev hole -> CHoleCan (goev ev) hole
  where
  goev = \case
    CtGiven p ev loc -> CtGiven (go p) ev loc
    _ -> error "substCt non given"
  go = substTy sigma
  gos = map go
