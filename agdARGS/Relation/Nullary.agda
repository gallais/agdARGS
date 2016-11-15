module agdARGS.Relation.Nullary where

open import Data.Bool
open import Function
open import Relation.Nullary

dec : ∀ {ℓ ℓ′} {A : Set ℓ} {P : Dec A → Set ℓ′} d → (∀ p → P (yes p)) → (∀ ¬p → P (no ¬p)) → P d
dec (yes p) y n = y p
dec (no ¬p) y n = n ¬p

dec′ :  ∀ {ℓ ℓ′} {A : Set ℓ} {P : Set ℓ′} (d : Dec A) → (∀ p → P) → (∀ ¬p → P) → P
dec′ = dec

toBool : ∀ {ℓ} {A : Set ℓ} → Dec A → Bool
toBool d = dec′ d (const true) (const false)

toSet : ∀ {ℓ} {A : Set ℓ} → Dec A → Set
toSet = T ∘ toBool

fromYes : ∀ {ℓ} {A : Set ℓ} (d : Dec A) {pr : toSet d} → A
fromYes (yes p) = p
fromYes (no ¬p) {}
