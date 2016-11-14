open import Level
open import Relation.Binary

module agdARGS.Data.Record.Properties
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Function
open import agdARGS.Data.Record STO
open import agdARGS.Data.UniqueSortedList STO
open import Relation.Binary.PropositionalEquality

[lookupTabulate] :
  {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
  (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ)
  {arg : _} (pr : arg ∈ args) → [lookup] pr ([tabulate] args ρ) ≡ ρ pr
[lookupTabulate] ρ z      = refl
[lookupTabulate] ρ (s pr) = [lookupTabulate] (ρ ∘ s) pr

lookupTabulate :
  {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
  (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ)
  {arg : _} (pr : arg ∈ args) → lookup pr (tabulate ρ) ≡ ρ pr
lookupTabulate = [lookupTabulate]
