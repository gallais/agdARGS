module agdARGS.System.Console.Options.Domain where

open import Level
open import Data.Unit
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Data.String
open import Function
open import agdARGS.Algebra.Magma

data Domain (ℓ : Level) : Set (suc ℓ) where
  Some : (S : Set ℓ)      → Domain ℓ
  ALot : (M : RawMagma ℓ) → Domain ℓ

elimDomain :
  {ℓ ℓᵖ : Level} {P : Domain ℓ → Set ℓᵖ}
  (dSome : ∀ S → P (Some S)) (dALot : ∀ M → P (ALot M)) →
  (d : Domain ℓ) → P d
elimDomain dSome dALot (Some S) = dSome S
elimDomain dSome dALot (ALot M) = dALot M

Carrier : {ℓ : Level} → Domain ℓ → Set ℓ
Carrier = elimDomain id RawMagma.Carrier

Parser : {ℓ : Level} → Domain ℓ → Set ℓ
Parser d = String → String ⊎ Carrier d