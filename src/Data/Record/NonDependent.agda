open import Relation.Binary.Definitions using (DecidableEquality)

module Data.Record.NonDependent (Label : Set) (eq? : DecidableEquality Label) where

open import Level using (Level; _⊔_)

open import Category.Applicative

open import Data.List.Fresh as Fresh using (List#)
open import Data.List.Fresh.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product as Prod using (∃; proj₁; proj₂; _,_)

open import Function.Base using (_∘_; _on_; id)

open import Relation.Nary using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; _because_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Unary using (Pred; IUniversal; _⇒_)

open import Stdlib

private
  variable
    a ℓ ℓ′ : Level
    v w : Pred Label a

Field : (Pred Label a) → Set a
Field = ∃

private
  variable
    p : Pred (Field v) ℓ

Fields : Pred Label a → Set a
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

map : {f : Pred (Field v) ℓ} {g : Pred (Field v) ℓ′} →
      ∀[ f ⇒ g ] → ∀[ Record f ⇒ Record g ]
map f (mkRecord rec) = mkRecord (All.map f rec)

_‼_ : ∀ {f : Field {a} v → Set ℓ} {flds : Fields v}
        (rec : Record f flds) (nm : Label) →
        {prf : True (isField? nm flds)} → f (theField (toWitness prf))
(rec ‼ nm) {prf} = All.lookup (rec .content) (toWitness prf)

open import Relation.Binary using (Rel)

module FreshExtra
       {r}
       {f : ∀ {ℓ} → Set ℓ → Set ℓ}
       (pure : ∀ {a} {A : Set a} → A → f A)
       (_<*>_ : ∀ {a b} {A : Set a} {B : Set b} → f (A → B) → f A → f B)
       {A : Set a} {R : Rel A r} {P : Pred A ℓ} {Q : Pred A ℓ′}
       where

  update : {xs : List# A R} →
           (ps : All P xs) (pos : Any Q xs) →
           let x = proj₁ (Any.witness pos) in
           (action : Q x → P x → f (P x)) → f (All P xs)
  update (px ∷ ps) (here qx)   action = pure (_∷ ps) <*> action qx px
  update (px ∷ ps) (there pos) action = pure (px ∷_) <*> update ps pos action

  traverse : {xs : List# A R} →
             (action : ∀ {x} → P x → f (Q x)) →
             (ps : All P xs) → f (All Q xs)
  traverse action []         = pure []
  traverse action (px ∷ pxs) = (pure _∷_ <*> action px) <*> traverse action pxs

module _
       {f : ∀ {ℓ} → Set ℓ → Set ℓ}
       (pure : ∀ {a} {A : Set a} → A → f A)
       (_<*>_ : ∀ {a b} {A : Set a} {B : Set b} → f (A → B) → f A → f B)
       {P : Pred (Field v) ℓ} {Q : Pred (Field v) ℓ′} {flds : Fields v}
       where

  update : Record P flds → (pos : Any Q flds) →
           let x = proj₁ (Any.witness pos) in
           (action : Q x → P x → f (P x)) → f (Record P flds)
  update (mkRecord rec) pos action =
    pure mkRecord <*> FreshExtra.update pure _<*>_ rec pos action

  traverse : (action : ∀ {x} → P x → f (Q x)) →
             (ps : Record P flds) → f (Record Q flds)
  traverse action (mkRecord rec)
    = pure mkRecord <*> FreshExtra.traverse pure _<*>_  action rec
