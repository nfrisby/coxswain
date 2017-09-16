{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fplugin=Coxswain #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=100 #-}

module Elm where

import Data.Sculls.Symbol
import GHC.TypeLits (type (+))
import Text.Read (readMaybe)

----- What is a Record?

frag1 = mkR .* #x .= 3 .* #y .= 4

frag2 = mkR .* #title .= "Steppenwolf" .* #author .= "Hesse" .* #pages .= 237

----- Access

point2D = mkR
  .* #x .= 0
  .* #y .= 0

point3D = mkR
  .* #x .= 3
  .* #y .= 4
  .* #z .= 12

-- PEOPLE

bill = mkR
  .* #name .= "Gates"
  .* #age .= 57

steve = mkR
  .* #name .= "Jobs"
  .* #age .= 56

larry = mkR
  .* #name .= "Page"
  .* #age .= 39

people =
  [ bill
  , steve
  , larry
  ]

----- Access

frag3 = (
    point3D `dot` #z
  ,
    bill `dot` #name
  ,
    (`dot` #name) bill
  ,
    map (`dot` #age) people
  )

frag4 = (
    point2D `dot` #x
  ,
    point3D `dot` #x
  ,
    (mkR .* #x .= 4) `dot` #x
  )

----- Pattern Matching   -- TODO: record patterns

frag5 !r =
  sqrt (x^2 + y^2)
  where
  x = r `dot` #x
  y = r `dot` #y

frag6 !r =
  age < 50
  where
  age = r `dot` #age

-----  Updating R Iecords

frag7 = (
    point2D ./* #y .= 1
  ,
    point3D ./* #x .= 0 ./* #y .= 0
  ,
    steve ./* #name .= "Wozniak"
  )

rawInput = mkR
  .* #name .= "Tom"
  .* #country .= "Finland"
  .* #age .= "34"
  .* #height .= "1.9"

prettify person = person
  ./* #age .= toInt (person `dot` #age)
  ./* #height .= toFloat (person `dot` #height)
  where
  toInt :: String -> Maybe Int
  toInt = readMaybe
  toFloat :: String -> Maybe Float
  toFloat = readMaybe

input =
  prettify rawInput

----- R Iecord Types

origin :: R I (Row0 .& "x" .= Float .& "y" .= Float)
origin = mkR
  .* #x .= 0
  .* #y .= 0

type Point = Row0
  .& "x" .= Float
  .& "y" .= Float

hypotenuse :: R I Point -> Float
hypotenuse !p =
  sqrt (x^2 + y^2)
  where
  x = p `dot` #x
  y = p `dot` #y

type Positioned a = a
  .& "x" .= Float
  .& "y" .= Float

type Named a = a
  .& "name" .= String

type Moving a = a
  .& "velocity" .= Float
  .& "angle" .= Float

lady :: R I (Named (Row0 .& "age" .= Int))
lady = mkR
  .* #name .= "Lois Lane"
  .* #age .= 31

dude :: R I (Named (Moving (Positioned Row0)))
dude = mkR
 .* #x .= 0
 .* #y .= 0
 .* #name .= "Clark Kent"
 .* #velocity .= 42
 .* #angle .= 30  -- degrees

getName ::
     (
       Lacks a "name"   -- Necessary difference compared to Elm. Comparable to KnownNat/KnownSymbol/etc.
     ,
       Short (NumCols a)   -- Merely consequence of particular record implemention.
     )
  => R I (Named a) -> String
getName !r = r `dot` #name

names :: [String]
names =
  [ getName dude, getName lady ]

getPos ::
     (
       Lacks a "y" , Lacks a "x"   -- Necessary difference compared to Elm. Comparable to KnownNat/KnownSymbol/etc.
     ,
       Short (NumCols a + 1)   -- Merely consequence of particular record implemention.
     )
  => R I (Positioned a) -> (Float,Float)
getPos !r = (x,y)
  where
  x = r `dot` #x
  y = r `dot` #y

positions :: [(Float,Float)]
positions =
  [ getPos origin, getPos dude ]

----- BEYOND THE ELM TUTORIAL

vars :: [V I (Row0 .& "x" .= Int .& "y" .= Char .& "z" .= Bool)]
vars = [inj #z True,inj #x 7,inj #y 'h',inj #z False,inj #y 'i',inj #x 3]

pvars = vpartition vars
