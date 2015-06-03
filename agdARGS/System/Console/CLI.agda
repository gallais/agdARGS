module agdARGS.System.Console.CLI where

open import Level
open import Data.Product
open import Data.String

open import agdARGS.Data.UniqueSortedList.Usual as UU
open import agdARGS.Data.Record.Usual

open import agdARGS.System.Console.Options.Domain
open import Function

mutual

  Command : (ℓ : Level) → Fields (suc ℓ) ("description" `∷ "modifiers" `∷ `[ "arguments" ])
  Command ℓ = Type $ "description" ∷= Lift String
                   ⟨ "modifiers"   ∷= Σ[ names ∈ USL ] Record names (Modifiers ℓ)
                   ⟨ "arguments"   ∷= Σ[ d ∈ Domain ℓ ] Parser d
                   ⟨ ⟨⟩

  Flag : (ℓ : Level) → Fields (suc ℓ) `[ "description" ]
  Flag ℓ = Type $ "description" ∷= Lift String
                ⟨ ⟨⟩
  Option : (ℓ : Level) → Fields (suc ℓ) ("description" `∷ `[ "arguments" ])
  Option ℓ = Type $ "description" ∷= Lift String
                  ⟨ "arguments"   ∷= Σ[ d ∈ Domain ℓ ] Parser d
                  ⟨ ⟨⟩

  data Modifier (ℓ : Level) (name : String) : Set (suc ℓ) where
    command : Record _ (Command ℓ) → Modifier ℓ name
    flag    : Record _ (Flag ℓ)    → Modifier ℓ name
    option  : Record _ (Option ℓ)  → Modifier ℓ name

  Modifiers : (ℓ : Level) {args : USL} → Fields (suc ℓ) args
  Modifiers ℓ = tabulate $ λ {s} → const (Modifier ℓ s)
