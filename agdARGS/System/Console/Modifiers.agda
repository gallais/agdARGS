module agdARGS.System.Console.Modifiers where

open import Level
open import Data.String
open import Data.Product
open import Function
open import agdARGS.Data.Record.Usual
open import agdARGS.System.Console.Options.Domain

Flag : (ℓ : Level) → Fields (suc ℓ) `[ "description" ]
Flag ℓ = Type $ "description" ∷= Lift String
              ⟨ ⟨⟩

Option : (ℓ : Level) → Fields (suc ℓ) ("description" `∷ `[ "arguments" ])
Option ℓ = Type $ "description" ∷= Lift String
                ⟨ "arguments"   ∷= Σ[ d ∈ Domain ℓ ] Parser d
                ⟨ ⟨⟩

data Modifier (ℓ : Level) (name : String) : Set (suc ℓ) where
  flag    : Record _ (Flag ℓ)    → Modifier ℓ name
  option  : Record _ (Option ℓ)  → Modifier ℓ name

toFields : ∀ ℓ {lb ub} {names : UniqueSortedList lb ub} → Fields (suc ℓ) names
toFields ℓ = tabulate $ λ {s} → const (Modifier ℓ s)

Modifiers : ∀ ℓ → Set (suc ℓ)
Modifiers ℓ = Σ[ names ∈ USL ] Record names (toFields ℓ)
