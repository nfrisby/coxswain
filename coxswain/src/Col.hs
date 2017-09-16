{-# LANGUAGE LambdaCase #-}

module Col where

import GHCAPI (Kind,Type,eqType)
import LowLevel (detCmpType)
import NormalForms

data ColumnNamePresence a =
    Absent
  |
    Present !a
  |
    UnknownPresence
    -- ^ The arguments are not determined enough to decide the
    -- presence.

lookupCol :: (Kind,Kind,Col) -> [(Kind,Kind,Col)] -> ColumnNamePresence (Maybe (Type,Type))
lookupCol (_,_,col0) = go
  where
  go = \case
    [] -> Absent
    (_,_,col):kcols -> case (col0,col) of

      (Col l t,Col m s)
        | Just cmp <- detCmpType m l
        -> if EQ == cmp then Present (Just (t,s)) else go kcols

      (ElseCol ty1,ElseCol ty2)
        | eqType ty1 ty2
        -> Present Nothing

      _ -> UnknownPresence
