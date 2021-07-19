module Data.Default where

record WithDefault {a} {A : Set a} (x : A) : Set a where
  field value : A
open WithDefault public

instance
  default : ∀ {a} {A : Set a} {x : A} → WithDefault x
  default {x = x} .value = x
