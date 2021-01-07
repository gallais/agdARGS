module Data.Record.Base {a} {A : Set a} where

open import Level using (Level)
open import Data.Nat.Base using (suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Vec.Relation.Unary.Any using (here; there; index)
open import Data.Vec.Relation.Unary.Unique.Propositional as Unique using (Unique; []; _∷_)
open import Function.Base using (const)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Function.Nary.NonDependent
open import Data.Product.Nary.NonDependent


private
  variable
    v : Level
    V : Set v

------------------------------------------------------------------------
-- Base Type

record Record {n} (ks : Vec A n) ..(Unique : Unique ks) -- keys
              {ls : Levels n} (fs : Sets n ls)   -- fields
              : Set (⨆ n ls) where
  field values : Product⊤ n fs
open Record public

------------------------------------------------------------------------
-- Constructors

empty : Record [] [] _
empty .values = _
<> = empty

cons : ∀ {n ks Unq ls fs} →
       ∀ k (k∉ks : All (k ≢_) ks) → V →
       Record {n} ks Unq {ls} fs → Record (k ∷ ks) (k∉ks ∷ Unq) (V , fs)
cons k k∉ks v r .values = v , r .values

------------------------------------------------------------------------
-- Destructors

head : ∀ {n ks Unq ls fs} → Record {suc n} ks Unq {ls} fs →
       proj₁ fs
head r = r .values .proj₁

tail : ∀ {n ks Unq ls fs} → Record {suc n} ks Unq {ls} fs →
       Record {n} (Vec.tail ks) (Unique.tail Unq) (proj₂ fs)
tail r .values = r .values .proj₂

------------------------------------------------------------------------
-- Lookup

lookup : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
         ∀ {k} → (k∈ks : k ∈ ks) → Projₙ fs (index k∈ks)
lookup r (here px)    = head r
lookup r (there k∈ks) = lookup (tail r) k∈ks

------------------------------------------------------------------------
-- UpdateAt

updateAt : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
           ∀ {k} (k∈ks : k ∈ ks) → (Projₙ fs (index k∈ks) → V) →
           Record ks Unq (Updateₙ fs (index k∈ks) V)
updateAt {Unq = _ ∷ _} r (here refl)  f = cons _ _ (f (head r)) (tail r)
updateAt {Unq = _ ∷ _} r (there k∈ks) f = cons _ _ (head r) (updateAt (tail r) k∈ks f)

------------------------------------------------------------------------
-- SetAt

setAt : ∀ {n ks Unq ls fs} → Record {n} ks Unq {ls} fs →
        ∀ {k} (k∈ks : k ∈ ks) → V → Record ks Unq (Updateₙ fs (index k∈ks) V)
setAt r k∈ks v = updateAt r k∈ks (const v)
