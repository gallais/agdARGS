module agdARGS.System.Console.CLI.Parser where

open import Level
open import Data.List
open import Data.String
open import Data.Sum
open import agdARGS.Data.Record.Usual
open import agdARGS.System.Console.CLI


mutual

  parseOption : {ℓ : Level} (c : Record _ (Option ℓ)) → String → String ⊎ {!!}
  parseOption = {!!}

  parseCommand : {ℓ : Level} (c : Record _ (Command ℓ)) → List String → String ⊎ {!!}
  parseCommand = {!!}

