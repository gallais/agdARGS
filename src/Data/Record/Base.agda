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

Levels : List A → Set a
Levels = All (λ _ → Level)

⨆ : ∀ {ks} → Levels ks → Level
⨆ []       = zero
⨆ (l ∷ ls) = l ⊔ (⨆ ls)

Fields : ∀ {ks} (ls : Levels ks) → Set (suc (⨆ ls))
Fields []       = Lift _ ⊤
Fields (l ∷ ls) = Set l × Fields ls

flookup : ∀ {k ks} (ls : Levels ks) →
          Fields ls → (k∈ks : k ∈ ks) → Set (All.lookup ls k∈ks)
flookup (l ∷ ls) (A , _)  (here refl)  = A
flookup (l ∷ ls) (_ , fs) (there k∈ks) = flookup ls fs k∈ks

Values : ∀ {ks} (ls : Levels ks) (fs : Fields ls) → Set (⨆ ls)
Values []       _        = ⊤
Values (l ∷ ls) (A , fs) = A × Values ls fs

vlookup : ∀ {k ks} (ls : Levels ks) {fs : Fields ls} →
          Values ls fs → (k∈ks : k ∈ ks) → flookup ls fs k∈ks
vlookup (l ∷ ls) (v , _)  (here refl)  = v
vlookup (l ∷ ls) (_ , vs) (there k∈ks) = vlookup ls vs k∈ks

record Record (ks : List A) ..(Unique : Unique ks) -- keys
              (ls : Levels ks) (fs : Fields ls)   -- fields
              : Set (⨆ ls) where
  field values : Values ls fs

  lookup : ∀ {k} (k∈ks : k ∈ ks) → flookup ls fs k∈ks
  lookup = vlookup ls values

open Record public hiding (lookup)

empty : Record [] [] [] _
empty .values = _
<> = empty

cons : ∀ {ks Unq ls fs} →
       ∀ k {v} {V : Set v} (k∉ks : All (¬_ ∘′ (k ≡_)) ks) → V →
       Record ks Unq ls fs → Record (k ∷ ks) (k∉ks ∷ Unq) (v ∷ ls) (V , fs)
cons k k∉ks v r .values = v , r .values
