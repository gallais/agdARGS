open import Level
open import Relation.Binary

module agdARGS.Data.Record.SmartConstructors
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Function
open import agdARGS.Relation.Nullary
open import agdARGS.Data.UniqueSortedList STO as USL hiding (module withEqDec)
open import agdARGS.Data.Record STO as Rec

Dummy : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args
Dummy ℓ = tabulate $ const $ Lift ⊤

⟨⟩ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Record args (Dummy ℓ)
⟨⟩ = pure go where
  go : {lb ub : _} {args : UniqueSortedList lb ub} (arg : _) (pr : arg ∈ args) →
       [lookup] pr (fields $ Dummy _)
  go arg z      = lift tt
  go arg (s pr) = go arg pr 

[update] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args →
           {arg : _} (pr : arg ∈ args) (A : Set ℓ) → [Fields] ℓ args
[update] (_ , fs) z      A = A , fs
[update] (f , fs) (s pr) A = f , [update] fs pr A

update : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args →
        {arg : _} (pr : arg ∈ args) (A : Set ℓ) → Fields ℓ args
update f pr A = mkFields $ [update] (fields f) pr A

infixr 5 [_at_∷=_⟨]_ _at_∷=_⟨_
[_at_∷=_⟨]_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
              (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
              [Record] args f → [Record] args ([update] f pr A)
[ a at z    ∷= v ⟨] (_ , r) = v , r
[ a at s pr ∷= v ⟨] (w , r) = w , [ a at pr ∷= v ⟨] r

_at_∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
            (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
            Record args f → Record args (update f pr A)
a at pr ∷= v ⟨ r = mkRecord $ [ a at pr ∷= v ⟨] content r

open import Relation.Binary.PropositionalEquality

module withEqDec
       (eqDec : Decidable ((StrictTotalOrder.Carrier STO → _ → Set ℓᵃ) ∋ _≡_))
       where

  open USL.withEqDec eqDec
  open import Relation.Nullary

  infixr 5 _∷=_⟨_
  _∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
           (arg : _) {A : Set ℓ} (v : A) (r : Record args f) {pr : toSet (arg ∈? args)} →
           Record args (update f (fromYes (arg ∈? args) {pr}) A)
  _∷=_⟨_ {args = args} arg v r {pr} with arg ∈? args
  ... | yes p = arg at p ∷= v ⟨ r
  ... | no ¬p = ⊥-elim pr

  `project : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
             (arg : _) (r : Record args f) → dec (arg ∈? args) (λ pr → lookup pr f) (const $ Lift ⊤)
  `project {args = args} arg r with arg ∈? args
  ... | yes pr = project pr r
  ... | no ¬pr = lift tt

  _‼_ : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} →
        Record args f → ∀ arg → {pr : toSet (arg ∈? args)} →
        lookup (fromYes (arg ∈? args) {pr}) f
  _‼_ {args = args} r arg {pr} with arg ∈? args
  ... | yes p = project p r
  ... | no ¬p = ⊥-elim pr
