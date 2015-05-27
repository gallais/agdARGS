open import Level
open import Relation.Binary

module agdARGS.Data.Record.SmartConstructors
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Product
open import Function
open import lib.Nullary
open import agdARGS.Data.Record STO as Rec hiding (module withEqDec)

[Dummy] : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args
[Dummy] ℓ = λ _ _ → Lift ⊤

Dummy : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args
Dummy ℓ = mkFields $ [Dummy] ℓ

project[_] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
             (r : Record args (mkFields $ λ _ _ → Set ℓ)) → Fields ℓ args
project[ r ] = mkFields $ λ arg pr → project arg pr r

⟨⟩ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Record args (Dummy ℓ)
⟨⟩ = pure $ λ _ _ → lift tt

[update] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args →
          {arg : _} (pr : arg ∈ args) (A : Set ℓ) → [Fields] ℓ args
[update] f z      A arg z       = A
[update] f z      A arg pr      = f arg pr
[update] f pr     A arg z       = f arg z
[update] f (s pr) A arg (s pr′) = [update] (λ a → f a ∘ s) pr A arg pr′

update : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args →
        {arg : _} (pr : arg ∈ args) (A : Set ℓ) → Fields ℓ args
update f pr A = mkFields $ [update] (content f) pr A

infixr 5 [_at_∷=_⟨]_ _at_∷=_⟨_
[_at_∷=_⟨]_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
              (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
              [Record] args f → [Record] args ([update] f pr A)
[ a at z    ∷= v ⟨] (_ , r) = v , r
[ a at s pr ∷= v ⟨] (w , r) = w , [ a at pr ∷= v ⟨] r


_at_∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
            (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
            Record args f → Record args (update f pr A)
a at pr ∷= v ⟨ r = mkRecord $ [ a at pr ∷= v ⟨] fields r

open import Relation.Binary.PropositionalEquality

module withEqDec
       (eqDec : Decidable ((StrictTotalOrder.Carrier STO → _ → Set ℓᵃ) ∋ _≡_))
       where

  open Rec.withEqDec eqDec
  open import Relation.Nullary

  infixr 5 _∷=_⟨_
  _∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
           (arg : _) {A : Set ℓ} (v : A) (r : Record args f) {pr : isYes (arg ∈? args)} →
           Record args (update f (fromYes (arg ∈? args) {pr}) A)
  _∷=_⟨_ {args = args} arg v r {pr} with arg ∈? args
  _∷=_⟨_ {args = args} arg v r      | yes pr = arg at pr ∷= v ⟨ r
  _∷=_⟨_ {args = args} arg v r {()} | no ¬pr