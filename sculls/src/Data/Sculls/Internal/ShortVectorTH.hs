{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Splices for "Data.Sculls.Internal.ShortVector".

module Data.Sculls.Internal.ShortVectorTH (
  dataTH,
  shortTH,
  ) where

import Language.Haskell.TH

import Data.Sculls.Internal.TH

-- | The data family and 'Applicative' instances. These are separate
-- from the @Short@ instance instances its @extend@ and @restrict@
-- methods reach up to @SV (n+1)@.
dataTH :: Int -> Q [Dec]
dataTH k =
      (++)
  <$>
      dataFamilyInstance k
  <*>
      applicativeInstance k

dataFamilyInstance :: Int -> Q [Dec]
dataFamilyInstance k = do
  let kind = Nothing
  let con = (nV k) >>= \n -> normalC n $ replicate k $ bangType (bang noSourceUnpackedness sourceStrict) (nm "a")
  let dStrat = Nothing
  let deriv = derivClause dStrat [conT n | n <- [
          ''Foldable
        ,
          ''Functor
        ,
          ''Traversable
        ] ]
  n <- nm "SV"
  (:[]) <$> dataInstD (cxt []) n [numT k,nm "a"] kind [con] [deriv]

applicativeInstance :: Int -> Q [Dec]
applicativeInstance k = fmap (:[]) $
  instanceD (cxt []) (conT ''Applicative `appT` (nm "SV" `appT` numT k))
    [pureDef k,inlinePragN 'pure,splatDef k,inlinePragN '(<*>)]

pureDef :: Int -> Q Dec
pureDef k = valD (varP 'pure) (normalB b) noWhere
  where
  b = lamE [if k > 0 then nm "a" else wildP] $ foldl appE (nV k) $ replicate k (nm "a")

splatDef :: Int -> Q Dec
splatDef k = valD (varP '(<*>)) (normalB b) noWhere
  where
  b =
     lamE [vecP k "f",vecP k "a"]
   $ foldl appE (nV k)
   $ [ nm f `appE` nm a | f <- names k "f" | a <- names k "a" ]

-- | The @Short@ instance; see 'dataTH'.
shortTH :: Int -> Q [Dec]
shortTH k = fmap (:[]) $
  instanceD (cxt []) (nm "Short" `appT` numT k)
    (   (($ k) <$> [selectDef,lensDef,extendDef,restrictDef,indicesDef])
     ++
        [inlinePrag "select",inlinePrag "lensSV",inlinePrag "extend",inlinePrag "restrict",inlinePrag "indices"]
    )

-- |
-- > select (V3 a b c) = \case
-- >   _ -> a
-- >   1 -> b
-- >   2 -> c
selectDef :: Int -> Q Dec
selectDef kp = valD (varP (mkName "select")) (normalB b) noWhere
  where
  k = kp + 1
  b = lamE [vecP k "a"] $ lamCaseE $ matches k $ map nm $ names k "a"

-- |
-- > lensSV f (V3 a b c) = \case
-- >   _ -> (\x -> V3 x b c) <$> f a
-- >   1 -> (\x -> V3 a x c) <$> f b
-- >   2 -> (\x -> V3 a b x) <$> f c
lensDef :: Int -> Q Dec
lensDef kp = valD (varP (mkName "lensSV")) (normalB b) noWhere
  where
  k = kp + 1
  b = lamE [nm "f",vecP k "a"] $ lamCaseE $ matches k [
              varE 'fmap
      `appE` (lamE [nm "x"] $ foldl appE (nV k) $ prefix $ nm "x" : suffix)
      `appE` (nm "f" `appE` nma)
    | (prefix,nma,suffix) <- contexts (nm <$> names k "a")
    ]

-- |
-- > extend (V3 a b c) x = \case
-- >   _ -> V4 x a b c
-- >   1 -> V4 a x b c
-- >   2 -> V4 a b x c
-- >   3 -> V4 a b c x
extendDef :: Int -> Q Dec
extendDef k = valD (varP (mkName "extend")) (normalB b) noWhere
  where
  b = lamE [vecP k "a",nm "x"] $ lamCaseE $ matches (k+1) [
      foldl appE (nV (k+1)) $ prefix $ nm "x" : suffix
    | (prefix,suffix) <- slots (nm <$> names k "a")
    ]

-- |
-- > restrict (V4 a b c d) = \case
-- >   _ -> (a,V3 b c d)
-- >   1 -> (b,V3 a c d)
-- >   2 -> (c,V3 a b d)
-- >   3 -> (d,V3 a b c)
restrictDef :: Int -> Q Dec
restrictDef k = valD (varP (mkName "restrict")) (normalB b) noWhere
  where
  b = lamE [vecP (k+1) "a"] $ lamCaseE $ matches (k+1) [
              conE '(,)
      `appE` nma
      `appE` (foldl appE (nV k) $ prefix suffix)
    | (prefix,nma,suffix) <- contexts (nm <$> names (k+1) "a")
    ]

-- |
-- > indices = V4 0 1 2 3
indicesDef :: Int -> Q Dec
indicesDef k = valD (varP (mkName "indices")) (normalB b) noWhere
  where
  b = foldl appE (nV k) $ map numE [0..k-1]

-----

inlinePragN :: Name -> Q Dec
inlinePragN n = pragInlD n Inline FunLike AllPhases

inlinePrag :: String -> Q Dec
inlinePrag s = pragInlD (mkName s) Inline FunLike AllPhases
