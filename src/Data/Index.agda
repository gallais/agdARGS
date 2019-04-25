module Data.Index where

open import Data.Fin.Base
open import Data.List.Base using (List; length; lookup)
open import Data.Nat
open import Data.Singleton
open import Relation.Nullary.Decidable

record Index {a} {A : Set a} (as : List A) (n : ℕ) : Set a where
  constructor mkIndex
  field {constraint} : True (n <? length as)
        singleton    : Singleton (lookup as (fromℕ≤ (toWitness constraint)))

pattern [_] k = mkIndex (indeed k)
