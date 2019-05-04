module Data.WithDefault where

open import Level
open import Data.Maybe.Base
open import Function

private
  variable
    a : Level
    A : Set a
    v : A

record WithDefault (A : Set a) (v : A) : Set a where
  constructor mkWithDefault
  field mvalue : Maybe A

  collapse : A
  collapse = fromMaybe v mvalue
open WithDefault using (collapse) public

pattern default = mkWithDefault nothing
pattern value v = mkWithDefault (just v)

setDefault : A → WithDefault A v → WithDefault A v
setDefault v default = value v
setDefault v d       = d

