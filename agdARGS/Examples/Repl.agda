module agdARGS.Examples.Repl where

open import Data.Nat     as Nat
open import Data.Integer as Int

open import Level as Level
open import Data.Empty
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Sum as Sum
open import Data.String as String
open import agdARGS.Data.String as Str
open import Data.List as List hiding ([_])
import agdARGS.Data.List as List
open import Function
open import agdARGS.Relation.Nullary


open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.CLI.Usage

open import agdARGS.Data.Error
open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read
open import agdARGS.Data.Integer.Read
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.Data.Record.Usual

open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.Options.Usual

cli : CLI _
cli = record
  { name = "agda-scheme"
  ; exec = record
    { description  = "Scheme, in Agda!"
    ; subcommands =
      , < "eval" ∷= record (basic string) { description = "Evaluate a line" }
      ⟨   "repl" ∷= record (basic none) { description =  "Read-eval-print loop" }
      ⟨ ⟨⟩
    ; modifiers   =
      , "-h"           ∷= flag "Display this help"
      ⟨ "--help"       ∷= flag "Display this help"
      ⟨ "--parse-only" ∷= flag "Parse but don't execute"
      ⟨ "--version"    ∷= flag "Output version information and exit"
      ⟨ ⟨⟩
    ; arguments    = none
    }
  }

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.System.Environment.Arguments

main : _
main = withCLI cli $ putStrLn ∘ success where

  success : ParsedInterface cli → String
  success (theCommand mods args) =
     if lower (mods ‼ "--help") ∨ lower (mods ‼ "-h")
     then usage cli
     else "Hello Here"
  success (subCommand name subc) = "Hello There"
