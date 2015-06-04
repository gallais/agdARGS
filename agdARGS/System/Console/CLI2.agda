{-# OPTIONS -v tc.pos:10 #-}

module agdARGS.System.Console.CLI2 where

open import Level
open import Data.Maybe
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.String

open import agdARGS.Data.UniqueSortedList.Usual as UU
open import agdARGS.Data.Record.Usual
open import agdARGS.Algebra.Magma

import agdARGS.System.Console.Options
open import agdARGS.System.Console.Options.Domain
open import Function


-- An element of type `[Fields] ℓ args` is a right-nested tuple of `Set ℓ`s.

-- `Fields ℓ args` is a record packing a `[Fields] ℓ args` (helps Agda fill
-- in implicits when `args` is concret and `[Fields]` reduces).

-- An element of type `[Record] args fs` is a right-nested tuple of elements
-- whose types are given by `fs : [Fields] ℓ args`

-- `Record args fs` packs a `[Record] args fs`.


-- Now the positivity issue:
-- - Defining Command₁ as a datatype                         works fine
-- - Defining Command₂ as a record with a `[Record] ⋯` field works fine
-- - Defining Command₃ as a record with a `Record ⋯`field    triggers an error

mutual

  data Command₁ : Set where
    mkCommand : String → String → (modifierNames : USL) →
                Record modifierNames (tabulate (λ {s} _ → Modifier s)) → Command₁

  record Command₂ : Set where
    inductive
    field
      name          : String
      description   : String
      modifierNames : USL
      modifiers     : [Record] modifierNames ([tabulate] _ (λ {s} _ → Modifier s))

  record Command₃ : Set where
    inductive
    field
      name          : String
      description   : String
      modifierNames : USL
      modifiers     : Record modifierNames (tabulate (λ {s} _ → Modifier s))

  data Modifier (name : String) : Set where
    command₁ : Command₁ → Modifier name
    command₂ : Command₂ → Modifier name
    command₃ : Command₃ → Modifier name