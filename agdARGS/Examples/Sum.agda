module agdARGS.Examples.Sum where

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
open import Data.List as List
import agdARGS.Data.List as List
open import Function
open import agdARGS.Relation.Nullary


open import agdARGS.System.Console.CLI
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

sum-cli : CLI Level.zero
sum-cli = record { name = "sum" ; exec = record
 { description = "Takes a list of number as an input and sums it"
 ; subcommands = , < "nat" ∷= record (basic $ lotsOf Nat) { description = "The inputs will be nats" }
                   ⟨ "int" ∷= record (basic $ lotsOf Int) { description = "The inputs will be ints" }
                   ⟨ ⟨⟩
 ; modifiers   = , "--version" ∷= flag "Output version information and exit"
                 ⟨ "-h"        ∷= flag "Display this help"
                 ⟨ ⟨⟩
 ; arguments   = none
 } }

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Environment.Arguments

main : _
main = withCLI sum-cli $ putStrLn ∘ success where

  sumNat : Maybe (List ℕ) → ℕ
  sumNat = maybe (List.foldr Nat._+_ 0) 0

  sumInt : Maybe (List ℤ) → ℤ
  sumInt = maybe (List.foldr Int._+_ (+ 0)) (+ 0)

  success : ParsedInterface sum-cli → String
  success ([                 ._ ∷= m & _ ])  =
         if lower (m ‼ "--version") then "Sum version: 0.1"
    else if lower (m ‼ "-h")        then usage sum-cli
    else ""
  success ([ ."int" [   z ]∙ ._ ∷= _ & vs ]) = Int.show     $ sumInt vs
  success ([ ."nat" [ s z ]∙ ._ ∷= _ & vs ]) = NatShow.show $ sumNat vs

  -- empty cases
  success ([ ."int" [      z   ]∙ _ [ () ]∙ _)
  success ([ ."nat" [ s    z   ]∙ _ [ () ]∙ _)
  success ([ _          [ s (s ()) ]∙ _)
