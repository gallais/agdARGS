open import Level using (Level)

module System.Console.CLI (l : Level) where

open Level using (suc)
import Level.Bounded as Level≤
open import Size using (Size; ↑_)

open import Data.List.Base using ([]; _∷_)
open import Data.String as String

open import Data.Record.Bounded.DecPropositional l String._≟_

record Command (name : String) (i : Size) : Set l
data Commands : Size → Set l

-- Unfortunately the level of indirection introduced by `Record` makes
-- the positivity checker fail to realise that all of this is just fine.
{-# NO_POSITIVITY_CHECK #-}
record Command name i where
  inductive
  field
    description : String
    commands    : Commands i
    modifiers   : {!!}
    arguments   : {!!}

SubCommands : ∀ {ks} → Size → Fields ks
SubCommands i .Fields.lookup {name} _ = Level≤.embed (Command name i)

data Commands where
  [_] : ∀ {i ns uniq} → Record {ns} uniq (SubCommands i) → Commands (↑ i)
