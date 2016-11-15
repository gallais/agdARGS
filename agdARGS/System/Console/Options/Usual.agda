module agdARGS.System.Console.Options.Usual where

open import Level
open import Data.Empty
open import Data.Product
open import Data.String
open import Data.List
open import Function
open import agdARGS.Algebra.Magma
open import agdARGS.Data.Error
open import agdARGS.System.Console.Options.Domain public

Arguments : (ℓ : Level) → Set (suc ℓ)
Arguments ℓ = Σ[ d ∈ Domain ℓ ] Parser d

none : ∀ {ℓ} → Arguments ℓ
none = Some (Lift ⊥) , const (throw "Argument provided when none expected")

lotsOf : ∀ {ℓ} {A : Set ℓ} → (String → Error A) → Arguments ℓ
lotsOf {ℓ} {A} p = ALot (List.rawMagma A) , ([_] <$>_) ∘ p
