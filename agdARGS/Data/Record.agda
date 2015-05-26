open import Level
open import Relation.Binary

module agdARGS.Data.Record
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Product
open import Function
open import Category.Applicative

-- A Record is characterised by a set of field names. We decide
-- to represent this set by a UniqueSortedList in order to ensure
-- unicity of field names. Hence the following import:

open import agdARGS.Data.UniqueSortedList STO

-- We then need to define what the content of each one of these
-- fields is. This is taken care of by associating a set to each
-- index of the UniqueSortedList of field names.

[Fields] : (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) → Set (suc ℓ ⊔ ℓʳ ⊔ ℓᵉ ⊔ ℓᵃ)
[Fields] ℓ args = (arg : _) (pr : arg ∈ args) → Set ℓ

record Fields (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) : Set (suc ℓ ⊔ ℓʳ ⊔ ℓᵉ ⊔ ℓᵃ) where
  constructor mkFields
  field
    content : [Fields] ℓ args
open Fields

[A[_,_]] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} →
           (a : Set ℓ → Set ℓ) → [Fields] ℓ args → [Fields] ℓ args
[A[ a , f ]] = λ arg pr → a (f arg pr)

A[_,_] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} →
         (a : Set ℓ → Set ℓ) → Fields ℓ args → Fields ℓ args
A[ a , f ] = mkFields [A[ a , content f ]]

-- A record is then defined by aggregating an element of each one
-- of these sets in a right-nested tuple.

[Record] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub) (f : [Fields] ℓ args) → Set ℓ
[Record] (lt ■)           f = Lift ⊤
[Record] (hd , lt ∷ args) f = f hd z × [Record] args (λ a → f a ∘ s)

record Record {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub) (f : Fields ℓ args) : Set ℓ where
  constructor mkRecord
  field
    fields : [Record] args (content f)
open Record

-- The first thing we expect Records to deliver is the ability to
-- project the content of a field given its name.

[project] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
            (arg : _) (prf : arg ∈ args) → [Record] args f → f arg prf
[project] arg z      (v , _) = v
[project] arg (s pr) (_ , r) = [project] arg pr r

project : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
          (arg : _) (prf : arg ∈ args) → Record args f → content f arg prf
project arg prf r = [project] arg prf $ fields r

-- If we know how to populate fields, we naturally want to be able
-- to build a record by tabulating the defining function.

[pure] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
         (v : (arg : _) (pr : arg ∈ args) → f arg pr) → [Record] args f
[pure] {args = lt ■}           v = lift tt
[pure] {args = hd , lt ∷ args} v = v _ z , [pure] (λ a → v a ∘ s)

pure : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
       (v : (arg : _) (pr : arg ∈ args) → content f arg pr) → Record args f
pure = mkRecord ∘ [pure]

-- A special sort of content may be a Fields-morphism: for each
-- field we will explaing how to turn data belonging to the first
-- type of Records to the second one.

infixr 3 _[⟶]_ _⟶_
_[⟶]_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (f : [Fields] ℓᶠ args) (g : [Fields] ℓᵍ args) → [Fields] (ℓᶠ ⊔ ℓᵍ) args
f [⟶] g = λ arg pr → f arg pr → g arg pr

_⟶_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (f : Fields ℓᶠ args) (g : Fields ℓᵍ args) → Fields (ℓᶠ ⊔ ℓᵍ) args
f ⟶ g = mkFields $ content f [⟶] content g

[app] : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
        {f : [Fields] ℓᶠ args} {g : [Fields] ℓᵍ args}
        (f→g : [Record] args (f [⟶] g)) (f : [Record] args f) → [Record] args g
[app] {args = lt ■}           f→g             f         = lift tt
[app] {args = hd , lt ∷ args} (f₀→g₀ , fₛ→gₛ) (f₀ , fₛ) = f₀→g₀ f₀ , [app] fₛ→gₛ fₛ

app : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
      {f : Fields ℓᶠ args} {g : Fields ℓᵍ args}
      (f→g : Record args (f ⟶ g)) (f : Record args f) → Record args g
app f→g f = mkRecord $ [app] (fields f→g) (fields f)

[seqA] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
         {a : Set ℓ → Set ℓ} (A : RawApplicative a) →
         [Record] args [A[ a , f ]] → a ([Record] args f)
[seqA] {ℓ} {args = args} {a = a} A = go args
  where
    module RA = RawApplicative A ; open RA

    go : {lb ub : _} (args : UniqueSortedList lb ub) {f : [Fields] ℓ args} →
         [Record] args [A[ a , f ]] → a ([Record] args f)
    go (lt ■)           r        = RA.pure r
    go (hd , lt ∷ args) (av , r) = _,_ RA.<$> av RA.⊛ go args r

seqA : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
       {a : Set ℓ → Set ℓ} (A : RawApplicative a) →
       Record args A[ a , f ] → a (Record args f)
seqA A r = mkRecord RA.<$> [seqA] A (fields r)
  where module RA = RawApplicative A