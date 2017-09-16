{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

-- | Splices for "Data.Sculls.Internal.RecordAndVariant".

module Data.Sculls.Internal.RecordAndVariantTH (
  genericsTH,
  rAllTH,
  ) where

import Coxswain (NRow(..))
import GHC.Generics
import Language.Haskell.TH
import Unsafe.Coerce (unsafeCoerce)

import Data.Sculls.Internal.TH

nrowT :: Int -> TypeQ
nrowT k = foldl snoc (promotedT 'NRow0) lts `sigT` (PromotedT ''NRow `AppT` VarT (mkName "kl") `AppT` VarT (mkName "kt"))
  where
  lts = reverse $ zip (names k "l") (names k "t")
  snoc p (l,t) = [t| 'NExt $p $(nm l) $(nm t) |]

-----

-- | The instances for GHC Generics.
genericsTH :: Int -> Q [Dec]
genericsTH k =
      (\x y -> [x,y])
  <$> instanceD (cxt []) (nm "GenericNR" `appT` nm "f" `appT` nrowT k `appT` numT k) (map inlinePrag ["toNR","fromNR"] ++ (($ k) <$> [repNRDef,fromNRDef,toNRDef]))
  <*> instanceD (cxt []) (nm "GenericNV" `appT` nm "f" `appT` nrowT k `appT` numT k) (map inlinePrag ["toNV","fromNV"] ++ (($ k) <$> [repNVDef,fromNVDef,toNVDef]))

repNRDef :: Int -> Q Dec
repNRDef k =
  tySynInstD (mkName "RepNR") $ tySynEqn [nm "f",nrowT k,numT k] $
    (nm "GDR" `appT` s) `appT` (nm "GCR" `appT` s `appT` prod)
  where
  s = strT ("R" ++ show k)
  times x y = [t| $x :*: $y |]
  prod = foldHalves times [t| U1 |] [
      nm "SGR" `appT` nm "f" `appT` nm l `appT` nm t
    | (l,t) <- zip (names k "l") (names k "t")
    ]

fromNRDef :: Int -> Q Dec
fromNRDef k = valD (nm "fromNR") (normalB b) noWhere
  where
  b = lamE [wildP,wildP,wildP,vecP k "a"] [e| M1 (M1 $prod) |]
  times x y = [e| $x :*: $y |]
  prod = foldHalves times [e| U1 |] [
      nm "sgr" `appE` nm a
    | a <- names k "a"
    ]

toNRDef :: Int -> Q Dec
toNRDef k = valD (nm "toNR") (normalB b) noWhere
  where
  b =
      lamE [wildP,wildP,wildP,[p| M1 (M1 $prod) |] ]
    $ foldl appE (nV k) [ [e| unsafeCoerce $(nm a) |] | a <- names k "a" ]
  times x y = [p| $x :*: $y |]
  prod = foldHalves times [p| U1 |] [ [p| M1 (K1 $(nm a)) |] | a <- names k "a" ]

repNVDef :: Int -> Q Dec
repNVDef k =
  tySynInstD (mkName "RepNV") $ tySynEqn [nm "f",nrowT k,numT k] $
    (nm "GDV" `appT` s) `appT` (nm "GCV" `appT` s `appT` prod)
  where
  s = strT ("V" ++ show k)
  times x y = [t| $x :+: $y |]
  prod = foldHalves times [t| V1 |] [
      nm "SGV" `appT` nm "f" `appT` nm l `appT` nm t
    | (l,t) <- zip (names k "l") (names k "t")
    ]

fromNVDef :: Int -> Q Dec
fromNVDef k = valD (nm "fromNV") (normalB b) noWhere
  where
  b = lamE [wildP,wildP,wildP,if k > 0 then nm "a" else wildP] [e| M1 . M1 . $cases |]
  cases = lamCaseE $ matches k prod
  times l r = map (\e -> [e| L1 $e |]) l ++ map (\e -> [e| R1 $e |]) r
  prod = foldHalves times [ [e| error "fromNV 0" |] ] $ replicate k [nm "sgv" `appE` nm "a"]

toNVDef :: Int -> Q Dec
toNVDef k = valD (nm "toNV") (normalB b) noWhere
  where
  b = lamE [wildP,wildP,wildP,if k > 0 then nm "k" else wildP] [e| $prod . unM1 . unM1 |]
  times l r = [e| either1 $l $r |]
  prod = foldHalves times [e| error "toNV 0" |] [
      lamE [ [p| M1 (K1 $(nm "a")) |] ] [e| $(nm "k") (unsafeCoerce $(nm "a")) $(numE i) |]
    | i <- [0..k-1]
    ]

-----

-- | The instances of 'RAll2'.
rAllTH :: Int -> Q [Dec]
rAllTH k = fmap (:[]) $ do
  let cs = [ nm "c" `appT` nm l `appT` nm t | l <- names k "l" | t <- names k "t" ]
  instanceD (cxt cs) (nm "RAll2" `appT` nm "c" `appT` nrowT k `appT` numT k) [inlinePrag "rdict_2",rdictDef k]

rdictDef :: Int -> Q Dec
rdictDef k = valD (nm "rdict_2") (normalB b) noWhere
  where
  b = lamE [wildP,wildP,wildP] $ foldl appE (varE 'unsafeCoerce) $ (:) (nV k) $
    [ nm "Dict" `sigE` (nm "D" `appT` nm "c" `appT` nm l `appT` nm t)
    | l <- names k "l"
    | t <- names k "t"
    ]

-----

inlinePrag :: String -> Q Dec
inlinePrag s = pragInlD (mkName s) Inline FunLike AllPhases
