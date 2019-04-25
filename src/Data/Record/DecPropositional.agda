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

------------------------------------------------------------------------
-- Re-export base types

open import Data.Record.Base {a} {A}
  as Record
  using ( Levels
        ; ⨆
        ; Fields
        ; Values
        ; Record
        ; values
        ; empty
        ; <>
        )
  public

------------------------------------------------------------------------
-- Smart constructors

cons : ∀ {ks Unq l ls f fs}
  k {k∉ks : True (all (¬? ∘ (k ≟_)) ks)} → f →
  Record ks Unq ls fs →
  Record (k ∷ ks) (toWitness k∉ks ∷ Unq) (l ∷ ls) (f , fs)
cons {ks} {Unq} k {k∉ks} v r = Record.cons {ks} {Unq} k (toWitness k∉ks) v r

infixr 5 _∷=_<_
_∷=_<_ = cons

------------------------------------------------------------------------
-- Smart lookup

lookup : ∀ {ks Unq ls fs} → Record ks Unq ls fs →
  ∀ k {k∈ks : True (any (k ≟_) ks)} → let k∈ks = toWitness k∈ks in
  Record.flookup ls fs k∈ks
lookup r k {k∈ks} = Record.lookup r (toWitness k∈ks)

infixl 4 _∙_
_∙_ = lookup

------------------------------------------------------------------------
-- Smart updateAt

updateAt : ∀ {u} {U : Set u} {ks Unq ls fs} →
  Record ks Unq ls fs →
  ∀ k {k∈ks : True (any (k ≟_) ks)} → let k∈ks = toWitness k∈ks in
  (Record.flookup ls fs k∈ks → U) →
  Record ks Unq (Record.lupdateAt ls k∈ks u) (Record.fupdateAt ls fs k∈ks U)
updateAt r k {k∈ks} f = Record.updateAt r (toWitness k∈ks) f

infixl 4 _[_]%=_
_[_]%=_ = updateAt

------------------------------------------------------------------------
-- Smart setAt

setAt : ∀ {u} {U : Set u} {ks Unq ls fs} →
  Record ks Unq ls fs →
  ∀ k {k∈ks : True (any (k ≟_) ks)} → let k∈ks = toWitness k∈ks in
  U → Record ks Unq (Record.lupdateAt ls k∈ks u) (Record.fupdateAt ls fs k∈ks U)
setAt r k {k∈ks} v = Record.setAt r (toWitness k∈ks) v

infixl 4 _[_]∷=_
_[_]∷=_ = setAt
