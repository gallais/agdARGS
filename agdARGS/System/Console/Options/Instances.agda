open import Level

module agdARGS.System.Console.Options.Instances (ℓ : Level) where

  open import Data.Unit
  open import Data.Bool
  open import Data.Sum as Sum
  open import Data.List
  open import Data.String
  open import Function

  open import agdARGS.Algebra.Magma
  open import agdARGS.System.Console.Options.Domain
  open import agdARGS.System.Console.Options
  private module Opts = Options ℓ
  open Opts

  flag : Option ℓ
  flag =
    record { name        = "Default name"
           ; description = "Default Description"
           ; flag        = ""
           ; optional    = true
           ; domain      = None
           ; parser      = lift tt
           }

  lotsOf : {A : Set ℓ} → (String → String ⊎ A) → Option ℓ
  lotsOf {A} p =
    record { name        = "Default name"
           ; description = "Default Description"
           ; flag        = ""
           ; optional    = true
           ; domain      = ALot (List.rawMagma A)
           ; parser      = Sum.map id [_] ∘ p
           }

  option : {A : Set ℓ} → (String → String ⊎ A) → Option ℓ
  option {A} p =
    record { name        = "Default name"
           ; description = "Default Description"
           ; flag        = ""
           ; optional    = true
           ; domain      = Some A
           ; parser      = p
           }