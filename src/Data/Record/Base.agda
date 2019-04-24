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
          (pr : k ∈ ks) → Fields ls → Set (All.lookup ls pr)
flookup (l ∷ ls) (here refl)  (A , _)  = A
flookup (l ∷ ls) (there pr)   (_ , fs) = flookup ls pr fs

Values : ∀ {ks} (ls : Levels ks) (fs : Fields ls) → Set (⨆ ls)
Values []       _        = ⊤
Values (l ∷ ls) (A , fs) = A × Values ls fs

vlookup : ∀ {k ks} (ls : Levels ks) {fs : Fields ls} →
          (pr : k ∈ ks) → Values ls fs → flookup ls pr fs
vlookup (l ∷ ls) (here refl) (v , _)  = v
vlookup (l ∷ ls) (there pr)  (_ , vs) = vlookup ls pr vs

record Record (ks : List A) ..(Unique : Unique ks) -- keys
              (ls : Levels ks) (fs : Fields ls)   -- fields
              : Set (⨆ ls) where
  field values : Values ls fs

  lookup : ∀ {k} (pr : k ∈ ks) → flookup ls pr fs
  lookup pr = vlookup ls pr values
open Record public hiding (lookup)

empty : Record [] [] [] _
empty .values = _
<> = empty

cons : ∀ {ks Unq ls fs} →
       ∀ k {v} {V : Set v} (k∉ks : All (¬_ ∘′ (k ≡_)) ks) → V →
       Record ks Unq ls fs → Record (k ∷ ks) (k∉ks ∷ Unq) (v ∷ ls) (V , fs)
cons k k∉ks v r .values = v , r .values
