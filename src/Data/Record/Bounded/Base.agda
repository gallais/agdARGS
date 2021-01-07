module Data.Record.Bounded.Base l {a} {A : Set a} where

open import Data.Unit.Polymorphic using (⊤)
open import Level as Level using (Level; Setω; _⊔_)
open import Level.Bounded as Level≤ using (Set≤; theSet; Lift; lift; lower)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there; index)
open import Data.List.Relation.Unary.Unique.Propositional as Unique using (Unique; []; _∷_)
open import Function.Base using (_∘_; const)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

private
  variable
    V : Set≤ l
    k : A
    ks : List A

------------------------------------------------------------------------
-- Base Type

module Fields where

  record Fields (ks : List A) : Setω where
    field lookup : ∀ {k} → k ∈ ks → Set≤ l
  open Fields public

  empty : Fields []
  empty .lookup = λ ()

  head : Fields (k ∷ ks) → Set≤ l
  head fs = fs .lookup (here refl)

  tail : Fields (k ∷ ks) → Fields ks
  tail fs .lookup p = fs .lookup (there p)

  cons : Set≤ l → Fields ks → Fields (k ∷ ks)
  cons f fs .lookup (here px) = f
  cons f fs .lookup (there p) = fs .lookup p

  setAt : Fields ks → k ∈ ks → Set≤ l → Fields ks
  setAt fs (here px) v = cons v (tail fs)
  setAt fs (there p) v = cons (head fs) (setAt (tail fs) p v)

open Fields using (Fields) hiding (module Fields) public

Values : (ks : List A) → Fields ks → Set l
Values []       fs = ⊤
Values (_ ∷ ks) fs = Lift (Fields.head fs) × Values ks (Fields.tail fs)

record Record {ks : List A} ..(Unique : Unique ks) -- keys
              (fs : Fields ks) : Set (a ⊔ l) where
  field values : Values ks fs
open Record public

------------------------------------------------------------------------
-- Constructors

empty : Record [] Fields.empty
empty .values = _
<> = empty

cons : ∀ {k ks fs} ..{uniq : Unique (k ∷ ks)} →
       theSet V → Record {ks} (Unique.tail uniq) fs →
       Record uniq (Fields.cons V fs)
cons v r .values = lift v , r .values

------------------------------------------------------------------------
-- Destructors

head : ∀ ..{uniq} {fs} → Record {k ∷ ks} uniq fs → theSet (Fields.head fs)
head r = lower (r .values .proj₁)

tail : ∀ ..{uniq} {fs} → Record {k ∷ ks} uniq fs →
       Record {ks} (Unique.tail uniq) (Fields.tail fs)
tail r .values = r .values .proj₂

------------------------------------------------------------------------
-- Lookup

lookup : ∀ ..{uniq} {fs} → Record uniq fs →
         ∀ {k} → (k∈ks : k ∈ ks) → theSet (Fields.lookup fs k∈ks)
lookup r (here refl)  = head r
lookup r (there k∈ks) = lookup (tail r) k∈ks

------------------------------------------------------------------------
-- UpdateAt

updateAt : ∀ ..{uniq} {fs} → Record uniq fs →
           ∀ {k} (k∈ks : k ∈ ks) → (theSet (Fields.lookup fs k∈ks) → theSet V) →
           Record uniq (Fields.setAt fs k∈ks V)
updateAt r (here refl)  f = cons (f (head r)) (tail r)
updateAt r (there k∈ks) f = cons (head r) (updateAt (tail r) k∈ks f)

------------------------------------------------------------------------
-- SetAt

setAt : ∀ {ks} ..{uniq} {fs} → Record uniq fs →
        ∀ {k} (k∈ks : k ∈ ks) → theSet V →
        Record uniq (Fields.setAt fs k∈ks V)
setAt r k∈ks v = updateAt r k∈ks (const v)
