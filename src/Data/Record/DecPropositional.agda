open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

module Data.Record.DecPropositional
  {a} {A : Set a} (_≟_ : Decidable {A = A} _≡_) where

open import Data.List.Base using (_∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; all)
open import Data.List.Relation.Unary.Any using (any)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Product
open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Data.Record.Base {a} {A} public

infixr 3 _∷=_<_
_∷=_<_ : ∀ {ks Unq l ls f fs}
         k {k∉ks : True (all (¬? ∘ (k ≟_)) ks)} → f →
         Record ks Unq ls fs →
         Record (k ∷ ks) (toWitness k∉ks ∷ Unq) (l ∷ ls) (f , fs)
_∷=_<_ {ks} {Unq} k {k∉ks} v r = cons {ks} {Unq} k (toWitness k∉ks) v r

lookup : ∀ {ks Unq ls fs} → Record ks Unq ls fs →
         ∀ k {k∈ks : True (any (k ≟_) ks)} → let k∈ks = toWitness k∈ks in
         flookup ls k∈ks fs
lookup r k {k∈ks} = Record.lookup r (toWitness k∈ks)
