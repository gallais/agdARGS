open import Relation.Binary using (DecidableEquality)

module Data.Record.Bounded.DecPropositional
  l {a} {A : Set a} (_≟_ : DecidableEquality A) where

open import Level using (Level)
open import Level.Bounded using (Set≤; theSet)
open import Data.List.Base using (_∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; all?)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Unique.Propositional using (_∷_)
open import Data.Product
open import Function
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

private
  variable
    V : Set≤ l

------------------------------------------------------------------------
-- Re-export base types

open import Data.Record.Bounded.Base l {a} {A}
  as Record
  using ( Record
        ; values
        ; <>
        ; head
        ; tail
        ; module Fields
        )
  public

------------------------------------------------------------------------
-- Smart constructors

cons : ∀ {ks uniq fs}
  k {k∉ks : True (all? (¬? ∘ (k ≟_)) ks)} → theSet V →
  Record uniq fs →
  Record (toWitness k∉ks ∷ uniq) (Fields.cons V fs)
cons k v r = Record.cons v r

infixr 5 _∷=_<_
_∷=_<_ = cons

------------------------------------------------------------------------
-- Smart lookup

lookup : ∀ {ks uniq fs} → Record uniq fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  theSet (Fields.lookup fs k∈ks)
lookup r k = Record.lookup r _

infixl 4 _∙_
_∙_ = lookup

------------------------------------------------------------------------
-- Smart updateAt

updateAt : ∀ {ks uniq fs} → Record uniq fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  (theSet (Fields.lookup fs k∈ks) → theSet V) →
  Record uniq (Fields.setAt fs k∈ks V)
updateAt r k f = Record.updateAt r _ f

infixl 4 _[_]%=_
_[_]%=_ = updateAt

------------------------------------------------------------------------
-- Smart setAt

setAt : ∀ {ks uniq fs} → Record uniq fs →
  ∀ k {k∈ks : True (k ∈? ks)} → let k∈ks = toWitness k∈ks in
  theSet V → Record uniq (Fields.setAt fs k∈ks V)
setAt r k v = updateAt r k (const v)

infixl 4 _[_]∷=_
_[_]∷=_ = setAt
