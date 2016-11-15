module agdARGS.System.Console.Modifiers where

open import Level
open import Data.String
open import Data.Product
open import Function
open import agdARGS.Data.Record.Usual as RU hiding (_∷=_⟨_)
open import agdARGS.System.Console.Options.Domain

Flag : (ℓ : Level) → Fields (suc ℓ) _
Flag ℓ = Type $ "description" RU.∷= Lift String
              ⟨ ⟨⟩

Option : (ℓ : Level) → Fields (suc ℓ) _
Option ℓ = Type $ "description" RU.∷= Lift String
                ⟨ "arguments"   RU.∷= Σ[ d ∈ Domain ℓ ] Parser d
                ⟨ ⟨⟩

data Modifier (ℓ : Level) (name : String) : Set (suc ℓ) where
  flag    : Record _ (Flag ℓ)    → Modifier ℓ name
  option  : Record _ (Option ℓ)  → Modifier ℓ name

mkFlag : ∀ {ℓ name} → String → Modifier ℓ name
mkFlag str = flag $ "description" RU.∷= lift str ⟨ ⟨⟩

toFields : ∀ ℓ {lb ub} {names : UniqueSortedList lb ub} → Fields (suc ℓ) names
toFields ℓ = tabulate $ λ {s} → const (Modifier ℓ s)

Modifiers : ∀ ℓ → Set (suc ℓ)
Modifiers ℓ = Σ[ names ∈ USL ] Record names (toFields ℓ)

infixr 5 _∷=_⟨_
_∷=_⟨_ : ∀ {ℓ} {args : USL} {fs : Fields (suc ℓ) args}
         (f : String) → Modifier ℓ f → Record args fs → Record _ _
f ∷= v ⟨ fs = f RU.∷= v ⟨ fs
