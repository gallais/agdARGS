module Data.Record.Base {a} {A : Set a} where

open import Level
open import Data.Unit
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.List.Membership.Propositional
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Base Type

Levels : List A → Set a
Levels = All (λ _ → Level)

⨆ : ∀ {ks} → Levels ks → Level
⨆ []       = zero
⨆ (l ∷ ls) = l ⊔ (⨆ ls)

Fields : ∀ {ks} (ls : Levels ks) → Set (suc (⨆ ls))
Fields []       = Lift _ ⊤
Fields (l ∷ ls) = Set l × Fields ls

Values : ∀ {ks} (ls : Levels ks) (fs : Fields ls) → Set (⨆ ls)
Values []       _        = ⊤
Values (l ∷ ls) (A , fs) = A × Values ls fs

record Record (ks : List A) ..(Unique : Unique ks) -- keys
              (ls : Levels ks) (fs : Fields ls)   -- fields
              : Set (⨆ ls) where
  field values : Values ls fs
open Record public

------------------------------------------------------------------------
-- Constructors

empty : Record [] [] [] _
empty .values = _
<> = empty

cons : ∀ {ks Unq ls fs} →
       ∀ k {v} {V : Set v} (k∉ks : All (¬_ ∘′ (k ≡_)) ks) → V →
       Record ks Unq ls fs → Record (k ∷ ks) (k∉ks ∷ Unq) (v ∷ ls) (V , fs)
cons k k∉ks v r .values = v , r .values

------------------------------------------------------------------------
-- Lookup

flookup : ∀ {k ks} (ls : Levels ks) →
          Fields ls → (k∈ks : k ∈ ks) → Set (All.lookup ls k∈ks)
flookup (l ∷ ls) (A , _)  (here refl)  = A
flookup (l ∷ ls) (_ , fs) (there k∈ks) = flookup ls fs k∈ks

vlookup : ∀ {k ks} (ls : Levels ks) {fs : Fields ls} →
          Values ls fs → (k∈ks : k ∈ ks) → flookup ls fs k∈ks
vlookup (l ∷ ls) (v , _)  (here refl)  = v
vlookup (l ∷ ls) (_ , vs) (there k∈ks) = vlookup ls vs k∈ks

lookup : ∀ {k ks Unq ls fs} →
  Record ks Unq ls fs → (k∈ks : k ∈ ks) → flookup ls fs k∈ks
lookup r = vlookup _ (r .values)

------------------------------------------------------------------------
-- UpdateAt

lupdateAt : ∀ {k ks} → Levels ks → k ∈ ks → Level → Levels ks
lupdateAt (_ ∷ ls) (here _)     u = u ∷ ls
lupdateAt (l ∷ ls) (there k∈ks) u = l ∷ lupdateAt ls k∈ks u

fupdateAt : ∀ {u k ks} (ls : Levels ks)
  (fs : Fields ls) (k∈ks : k ∈ ks) → Set u →
  Fields (lupdateAt ls k∈ks u)
fupdateAt (_ ∷ ls) (_ , fs) (here refl)  U = U , fs
fupdateAt (l ∷ ls) (f , fs) (there k∈ks) U = f , fupdateAt ls fs k∈ks U

vupdateAt : ∀ {u} {U : Set u} {k ks} ls {fs} →
  Values ls fs → (k∈ks : k ∈ ks) →
  (flookup ls fs k∈ks → U) →
  Values (lupdateAt ls k∈ks u) (fupdateAt ls fs k∈ks U)
vupdateAt (_ ∷ ls) (v , vs) (here refl)  f = f v , vs
vupdateAt (l ∷ ls) (v , vs) (there k∈ks) f = v , vupdateAt ls vs k∈ks f

updateAt : ∀ {u} {U : Set u} {k ks Unq ls fs} →
  Record ks Unq ls fs → (k∈ks : k ∈ ks) →
  (flookup ls fs k∈ks → U) →
  Record ks Unq (lupdateAt ls k∈ks u) (fupdateAt ls fs k∈ks U)
updateAt r k∈ks f .values = vupdateAt _ (r .values) k∈ks f

------------------------------------------------------------------------
-- SetAt

setAt : ∀ {u} {U : Set u} {k ks Unq ls fs} →
  Record ks Unq ls fs → (k∈ks : k ∈ ks) → U →
  Record ks Unq (lupdateAt ls k∈ks u) (fupdateAt ls fs k∈ks U)
setAt r k∈ks v = updateAt r k∈ks (const v)
