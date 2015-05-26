open import Level
open import Relation.Binary

module agdARGS.Data.Record.SmartConstructors
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Product
open import Function
open import agdARGS.Data.Record STO

[Dummy] : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args
[Dummy] ℓ = λ _ _ → Lift ⊤

Dummy : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args
Dummy ℓ = mkFields $ [Dummy] ℓ

project[_] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
             (r : Record args (mkFields $ λ _ _ → Set ℓ)) → Fields ℓ args
project[ r ] = mkFields $ λ arg pr → project arg pr r

⟨⟩ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Record args (Dummy ℓ)
⟨⟩ = pure $ λ _ _ → lift tt

[epgzh] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args →
          {arg : _} (pr : arg ∈ args) (A : Set ℓ) → [Fields] ℓ args
[epgzh] f z      A arg z       = A
[epgzh] f z      A arg pr      = f arg pr
[epgzh] f pr     A arg z       = f arg z
[epgzh] f (s pr) A arg (s pr′) = [epgzh] (λ a → f a ∘ s) pr A arg pr′

epgzh : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args →
        {arg : _} (pr : arg ∈ args) (A : Set ℓ) → Fields ℓ args
epgzh f pr A = mkFields $ [epgzh] (content f) pr A

infixr 5 [_at_∷=_⟨]_ _at_∷=_⟨_
[_at_∷=_⟨]_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
              (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
              [Record] args f → [Record] args ([epgzh] f pr A)
[ a at z    ∷= v ⟨] (_ , r) = v , r
[ a at s pr ∷= v ⟨] (w , r) = w , [ a at pr ∷= v ⟨] r


_at_∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
            (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
            Record args f → Record args (epgzh f pr A)
a at pr ∷= v ⟨ r = mkRecord $ [ a at pr ∷= v ⟨] fields r
