open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Record.NonDependent (Label : Set) (eq? : DecidableEquality Label) where

open import Level using (Level; _⊔_)

open import Data.List.Fresh as Fresh using (List#)
open import Data.List.Fresh.Relation.Unary.All as All using (All)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any)
open import Data.Product as Prod using (∃; proj₁; proj₂; _,_)

open import Function.Base using (_∘_; _on_; id)

open import Relation.Nary using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; _because_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (IUniversal; _⇒_)

open import Stdlib

private
  variable
    a ℓ ℓ′ : Level
    v w : Label → Set a

Field : (Label → Set a) → Set a
Field = ∃

private
  variable
    p : Field v → Set ℓ

Fields : (Label → Set a) → Set a
Fields v = List# (Field v) (λ f₁ f₂ → ⌊ ¬? (eq? (proj₁ f₁) (proj₁ f₂)) ⌋)

module Fields where

  map : ∀[ v ⇒ w ] → Fields v → Fields w
  map f = Fresh.map (Prod.map₂ f) id

IsField : (nm : Label) → (flds : Fields {a} v) → Set a
IsField nm = Any (λ fld → ⌊ eq? nm (proj₁ fld) ⌋)

isField? : (nm : Label) → (flds : Fields v) → Dec (IsField nm flds)
isField? nm = Any.any? λ fld → lift? (true? (eq? nm  (proj₁ fld)))

theField : {flds : Fields v} → Any p flds → Field v
theField = proj₁ ∘ Any.witness

record Record (f : Field {a} v → Set ℓ) (flds : Fields v) : Set (a ⊔ ℓ) where
  constructor mkRecord
  field content : All f flds
open Record public

map : {f : Field v → Set ℓ} {g : Field v → Set ℓ′} →
      ∀[ f ⇒ g ] → ∀[ Record f ⇒ Record g ]
map f (mkRecord rec) = mkRecord (All.map f rec)

_‼_ : ∀ {f : Field {a} v → Set ℓ} {flds : Fields v}
        (rec : Record f flds) (nm : Label) →
        {prf : True (isField? nm flds)} → f (theField (toWitness prf))
(rec ‼ nm) {prf} = All.lookup (rec .content) (toWitness prf)
