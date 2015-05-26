module agdARGS.Data.Record.Examples where

open import Level as Level
open import Data.Unit
open import Data.String
open import Data.Nat as Nat
open import Data.Product
open import Data.Maybe
open import Category.Monad
open import lib.Nullary

open import agdARGS.Data.UniqueSortedList.Examples
open import agdARGS.Data.Record                   strictTotalOrder
open import agdARGS.Data.Record.SmartConstructors strictTotalOrder

open import Function

[Sets] : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] (Level.suc ℓ) args
[Sets] ℓ = λ _ _ → Set ℓ

Sets : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields (Level.suc ℓ) args
Sets ℓ = mkFields ([Sets] ℓ)

[⟦_⟧] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} (r : [Record] args $ [Sets] ℓ) → [Fields] ℓ args
[⟦ r ⟧] = λ arg pr → [project] arg pr r

⟦_⟧ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} (r : Record args $ Sets ℓ) → Fields ℓ args
⟦ r ⟧ = mkFields [⟦ fields r ⟧]

CharacteristicsDomain : Fields _ Characteristics
CharacteristicsDomain = ⟦ mkRecord (fields f) ⟧
  where
    f : Record Characteristics _
    f = "age"  at z   ∷= ℕ
      ⟨ "name" at s z ∷= String
      ⟨ ⟨⟩

Person : Set
Person = Record Characteristics CharacteristicsDomain

julie : Person
julie = mkRecord $ fields r
  where
  r : Record Characteristics _
  r = "age"  at   z ∷= 22     
    ⟨ "name" at s z ∷= "julie"
    ⟨ ⟨⟩

john : Person
john = mkRecord $ 17 , "john" , lift tt

getsInThePub : Record Characteristics (CharacteristicsDomain ⟶ A[ Maybe , CharacteristicsDomain ])
getsInThePub = mkRecord $ checkAge , AM.pure , lift tt
  where
    module AM = RawMonad monad

    checkAge : ℕ → Maybe ℕ
    checkAge age = dec (18 Nat.≤? age) (const $ AM.pure age) (const $ nothing)

pubValidator : Person → Maybe Person
pubValidator = seqA AM.rawIApplicative ∘ app getsInThePub
  where module AM = RawMonad monad

johnInThePub : Maybe Person
johnInThePub = pubValidator john

julieInThePub : Maybe Person
julieInThePub = pubValidator julie



