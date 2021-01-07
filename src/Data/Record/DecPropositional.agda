open import Relation.Binary using (DecidableEquality)

module Data.Record.DecPropositional
  {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Level using (Level)
open import Data.Nat.Base using (suc)
open import Data.Vec.Base using (_∷_)
open import Data.Vec.Relation.Unary.All using (All; _∷_; all?)
open import Data.Vec.Relation.Unary.Any using (index)
open import Data.Vec.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.Vec.Relation.Unary.Unique.Propositional using (_∷_)
open import Data.Product
open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import Data.Product.Nary.NonDependent using (Projₙ; Updateₙ)

private
  variable
    v : Level
    V : Set v

------------------------------------------------------------------------
-- Re-export base types

open import Data.Record.Base {a} {A}
  as Record
  using ( Record
        ; values
        ; <>
        ; head
        ; tail
        )
  public

------------------------------------------------------------------------
-- Smart constructors

cons : ∀ {n ks Unq l ls f fs}
  k {k∉ks : True (all? (¬? ∘ (k ≟_)) ks)} → f →
  Record {n} ks Unq {ls} fs →
  Record {suc n} (k ∷ ks) (toWitness k∉ks ∷ Unq) {l , ls} (f , fs)
cons k {k∉ks} v r = Record.cons k (toWitness k∉ks) v r

infixr 5 _∷=_<_
_∷=_<_ = cons

------------------------------------------------------------------------
-- Smart lookup

lookup : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  Projₙ fs (index k∈ks)
lookup r k {k∈ks} = Record.lookup r (toWitness k∈ks)

infixl 4 _∙_
_∙_ = lookup

------------------------------------------------------------------------
-- Smart updateAt

updateAt : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  (Projₙ fs (index k∈ks) → V) → Record ks Unq (Updateₙ fs (index k∈ks) V)
updateAt r k {k∈ks} f = Record.updateAt r (toWitness k∈ks) f

infixl 4 _[_]%=_
_[_]%=_ = updateAt

------------------------------------------------------------------------
-- Smart setAt

setAt : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  V → Record ks Unq (Updateₙ fs (index k∈ks) V)
setAt r k {k∈ks} v = Record.setAt r (toWitness k∈ks) v

infixl 4 _[_]∷=_
_[_]∷=_ = setAt
