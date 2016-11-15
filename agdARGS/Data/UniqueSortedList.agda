open import Level
open import Relation.Binary

module agdARGS.Data.UniqueSortedList
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Function
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Maybe as Maybe
open import agdARGS.Relation.Nullary
open import Relation.Nullary
open import Category.Monad
open import agdARGS.Data.Infinities

module ISTO = StrictTotalOrder (StrictTotalOrderT STO)
open ISTO
open ISTO using (_<_ ; compare) public

infix  7 _■
infixr 6 _,_∷_
data UniqueSortedList (lb ub : Carrier) : Set (ℓᵃ ⊔ ℓʳ) where
  _■    : .(lt : lb < ub) → UniqueSortedList lb ub
  _,_∷_ : ∀ hd .(lt : lb < ↑ hd) (tl : UniqueSortedList (↑ hd) ub) → UniqueSortedList lb ub

weaken : ∀ {a b c} .(pr : a < b) → UniqueSortedList b c → UniqueSortedList a c
weaken le₁ (le₂ ■)         = trans le₁ le₂ ■
weaken le₁ (hd , le₂ ∷ xs) = hd , trans le₁ le₂ ∷ xs

insert : ∀ a {lb ub} .(lt₁ : lb < ↑ a) .(lt₂ : ↑ a < ub) →
         UniqueSortedList lb ub → Maybe $ UniqueSortedList lb ub
insert a lt₁ lt₂ (_ ■)          = just (a , lt₁ ∷ lt₂ ■)
insert a lt₁ lt₂ (hd , lt′ ∷ xs) with compare (↑ a) (↑ hd)
... | tri< lt  ¬eq ¬gt = just (a , lt₁ ∷ hd , lt ∷ xs)
... | tri≈ ¬lt eq  ¬gt = nothing
... | tri> ¬lt ¬eq gt  = Maybe.map (_,_∷_ hd lt′) (insert a gt lt₂ xs)

insert′ : ∀ a {lb ub} .(lt₁ : lb < ↑ a) .(lt₂ : ↑ a < ub) →
          UniqueSortedList lb ub → UniqueSortedList lb ub
insert′ a lt₁ lt₂ (_ ■)          = a , lt₁ ∷ lt₂ ■
insert′ a lt₁ lt₂ (hd , lt′ ∷ xs) with compare (↑ a) (↑ hd)
... | tri< lt  ¬eq ¬gt = a , lt₁ ∷ hd , lt ∷ xs
... | tri≈ ¬lt eq  ¬gt = hd , lt′ ∷ xs
... | tri> ¬lt ¬eq gt  = hd , lt′ ∷ insert′ a gt lt₂ xs

import Data.List as List
open List using (List)

fromList : List (StrictTotalOrder.Carrier STO) → Maybe $ UniqueSortedList -∞ +∞
fromList = List.foldr (λ el xs → xs >>= insert el (-∞<↑ el) ↑ el <+∞) $ just (-∞<+∞ ■)
  where open RawMonad Maybe.monad

infix 5 _∈_
data _∈_ (a : _) {lb ub : Carrier} : UniqueSortedList lb ub → Set (ℓᵉ ⊔ ℓʳ) where
  z : ∀ {xs} .{lt}            → a ∈ a , lt ∷ xs
  s : ∀ {b xs} .{lt} → a ∈ xs → a ∈ b , lt ∷ xs

open import Relation.Binary.PropositionalEquality

∈∷-inj : ∀ {a lb hd} .{le : lb < ↑ hd} {ub} {xs : UniqueSortedList (↑ hd) ub} →
       a ∈ hd , le ∷ xs → a ≡ hd ⊎ a ∈ xs
∈∷-inj z      = inj₁ refl
∈∷-inj (s pr) = inj₂ pr


search : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {R : Rel A ℓ₂} (d : Decidable R) (f : _ → A)
       (a : A) {lb ub : _} (xs : UniqueSortedList lb ub) → Dec (Σ[ el ∈ _ ] (el ∈ xs × R (f el) a))
search d f a (le ■)         = no $ λ { (_ , () , _) }
search {R = R} d f a (hd , lt ∷ xs) with d (f hd) a | search d f a xs
... | yes p | _                = let open IsEquivalence (StrictTotalOrder.isEquivalence STO)
                               in yes (hd , z , p)
... | _     | yes (el , p , r) = yes (el , s p , r)
... | no ¬p | no ¬q            = no (λ { (el , p⊎q , r) → [ (λ p → ¬p (subst (λ x → R (f x) a) p r))
                                                        , (λ q → ¬q (el , q , r)) ]′ (∈∷-inj p⊎q)  })

module withEqDec
       (eqDec : Decidable ((StrictTotalOrder.Carrier STO → _ → Set ℓᵃ) ∋ _≡_))
       where

  _∈?_ : (a : _) {lb ub : Carrier} (as : UniqueSortedList lb ub) → Dec (a ∈ as)
  a ∈? as with search eqDec id a as
  ... | yes (.a , pr , refl) = yes pr
  ... | no ¬pr               = no $ λ pr → ¬pr $ _ , pr , refl
