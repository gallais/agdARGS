open import Level

module agdARGS.Data.Arguments.Instances (ℓ : Level) where

  open import Data.Unit
  open import Data.Bool
  open import Data.Sum as Sum
  open import Data.List
  open import Data.String
  open import Function

  open import agdARGS.Algebra.Magma
  open import agdARGS.Data.Arguments
  module Args = Arguments ℓ
  open Args

  flag : Argument ℓ
  flag =
    record { name        = "Default name"
           ; description = "Default Description"
           ; flag        = ""
           ; optional    = true
           ; domain      = None
           ; parser      = lift tt
           }

  lotsOf : {A : Set ℓ} → (String → String ⊎ A) → Argument ℓ
  lotsOf {A} p =
    record { name        = "Default name"
           ; description = "Default Description"
           ; flag        = ""
           ; optional    = true
           ; domain      = ALot (List.rawMagma A)
           ; parser      = Sum.map id [_] ∘ p
           }