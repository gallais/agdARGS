module agdARGS.Data.Record.Examples where

open import Level as Level
open import Data.Unit
open import Data.Bool
open import Data.Nat as Nat
open import Data.String
open import Data.Product
open import Data.Maybe
open import Category.Monad
open import agdARGS.Relation.Nullary

open import agdARGS.Data.UniqueSortedList.Examples
open import agdARGS.Data.Record.Usual

open import Function

-- We can apply this new method to Characteristics for instance

Attributes : Fields Level.zero Characteristics
Attributes = Type $ "age"    ∷= ℕ
                  ⟨ "name"   ∷= String
                  ⟨ "idcard" ∷= Bool
                  ⟨ ⟨⟩

-- A Person is then modelled as a record of attributes for each one
-- her characterics

Person : Set
Person = Record Characteristics Attributes

-- We may either build the nested tuple directly but that
-- requires understanding the internal representation:
--|| "age" :: "name" :: "idcard" :: []
-- has been sorted to
--|| "age" :: "idcard" :: "name" :: []

john : Person
john = mkRecord $ 17 , true , "john" , lift tt

-- Or we may use the smart constructors requiring us to prove
-- that the field indeed exists. Once more we have to know
-- that "name", for instance, is at index s (s z)

june : Person
june = "age"    at z       ∷= 20
     ⟨ "name"   at s (s z) ∷= "june"
     ⟨ "idcard" at s z     ∷= true
     ⟨ ⟨⟩

-- Or, given that equality on Strings is decidable, we may
-- rely on a decision procedure to generate this information
-- and write the simpler:

julie : Person
julie = "age"    ∷= 22     
      ⟨ "name"   ∷= "julie"
      ⟨ "idcard" ∷= false
      ⟨ ⟨⟩

-- Once we have our Persons, we can write an (applicative) validator
-- by specifying validators for each one of the fields. Here we
-- assume they want to get in a pub. To do that, they need to:
-- - be over 18
-- - be carrying an id

getsInThePub : Record Characteristics (Attributes ⟶ Maybe [ Attributes ])
getsInThePub = "age"    ∷= checkAge    
             ⟨ "name"   ∷= AM.pure
             ⟨ "idcard" ∷= checkId
             ⟨ ⟨⟩
  where
    module AM = RawMonad monad

    checkAge : ℕ → Maybe ℕ
    checkAge age = dec (18 Nat.≤? age) (const $ AM.pure age) (const $ nothing)

    checkId : Bool → Maybe Bool
    checkId b = if b then just b else nothing

-- the validator then runs the various tests

pubValidator : Person → Maybe Person
pubValidator = seqA AM.rawIApplicative ∘ app getsInThePub
  where module AM = RawMonad monad

-- We can now check for each one of them whether they will be
-- able to get in the pub. Looks like june is going to have to
-- drink alone...

johnInThePub : Maybe Person
johnInThePub = pubValidator john

juneInThePub : Maybe Person
juneInThePub = pubValidator june

julieInThePub : Maybe Person
julieInThePub = pubValidator julie
