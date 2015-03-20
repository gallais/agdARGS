module agdARGS.System.Console.Options.Domain where

open import Level
open import Data.Unit
open import Data.Sum
open import Data.Maybe
open import Data.String
open import Function
open import agdARGS.Algebra.Magma

data Domain (ℓ : Level) : Set (suc ℓ) where
  None :                    Domain ℓ
  Some : (S : Set ℓ)      → Domain ℓ
  ALot : (M : RawMagma ℓ) → Domain ℓ

elimDomain :
  {ℓ ℓᵖ : Level} {P : Domain ℓ → Set ℓᵖ}
  (dNone : P None) (dSome : ∀ S → P (Some S)) (dALot : ∀ M → P (ALot M)) →
  (d : Domain ℓ) → P d
elimDomain dNone dSome dALot None     = dNone
elimDomain dNone dSome dALot (Some S) = dSome S
elimDomain dNone dSome dALot (ALot M) = dALot M

Carrier : {ℓ : Level} → Domain ℓ → Maybe (Set ℓ)
Carrier = elimDomain nothing just $ just ∘ RawMagma.Carrier

Parser : {ℓ : Level} → Domain ℓ → Set ℓ
Parser = maybe (λ S → String → String ⊎ S) (Lift ⊤) ∘ Carrier