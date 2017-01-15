module agdARGS.Examples.Grep where

open import Data.Product
open import Data.String
open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.CLI.Usage
open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.Options.Usual
open import agdARGS.Data.UniqueSortedList.Usual
open import Function
open import IO

Grep : CLI _
Grep = record
  { name     = "grep"
  ; exec     = record
  { description  = "Print lines matching a regexp"
  ; subcommands  = noSubCommands
  ; arguments    = lotsOf filePath
  ; modifiers    = 
    , "-v" ∷= flag "Invert match"
    ⟨ "-i" ∷= flag "Ignore case"
    ⟨ "-e" ∷= option "Regexp" regexp
    ⟨ ⟨⟩
  }}

main = withCLI Grep $ const $ putStrLn $ usage Grep
