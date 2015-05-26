module agdARGS.Data.Record.Examples where

open import Level
open import Data.Unit
open import Data.String
open import Data.Nat as Nat
open import Data.Product
open import Data.Maybe
open import Category.Monad
open import lib.Nullary

open import agdARGS.Data.UniqueSortedList.Examples
open import agdARGS.Data.Record strictTotalOrder

open import Function

CharacteristicsDomain : Fields _ Characteristics
CharacteristicsDomain = mkFields $ λ arg pr → project arg pr (mkRecord (ℕ , String , lift tt))

Person : Set
Person = Record Characteristics CharacteristicsDomain

julie : Person
julie = mkRecord $ 22 , "julie" , lift tt

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

