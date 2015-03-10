module agdARGS.Data.Sum where

open import Level
open import Data.Sum
open import Function
open import Category.Monad

monad : {ℓᵃ : Level} (A : Set ℓᵃ) {ℓᵇ : Level} →
        RawMonad ((Set (ℓᵃ ⊔ ℓᵇ) → Set (ℓᵃ ⊔ ℓᵇ)) ∋ _⊎_ A )
monad A {ℓᵇ} =
  record { return = inj₂
         ; _>>=_ = [ flip (const inj₁) , flip _$_ ]′ }