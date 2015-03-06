module agdARGS.Data.List where

open import Level using (Level)
open import Data.Nat
open import Data.List

repeat : {ℓ : Level} {A : Set ℓ} (n : ℕ) (a : A) → List A
repeat zero    a = []
repeat (suc n) a = a ∷ repeat n a