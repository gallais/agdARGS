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
open import agdARGS.System.Console.CLI.Parser

open import agdARGS.Data.Error
open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read
open import agdARGS.Data.Integer.Read
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.Data.Record.Usual

open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Modifiers as Mods using (mkFlag)
open import agdARGS.System.Console.Options.Usual

sum-cli : CLI Level.zero
sum-cli = record { name = "sum"
                 ; exec = sum-exec } where

  sum-exec = record { description = "sum"
                    ; subcommands = , commands sum-exec-subs
                    ; modifiers   = , sum-exec-mods
                    ; arguments   = none
                    } where

    sum-exec-mods = "--version" Mods.∷= mkFlag "Output version information and exit" ⟨ ⟨⟩
    sum-exec-subs = "nat" ∷= basic "exec" (lotsOf parseℕ)
                  ⟨ "int" ∷= basic "exec" (lotsOf parseℤ)
                  ⟨ ⟨⟩

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.System.Environment.Arguments

main : _
main = run $
  ♯ getArgs IO.>>= λ args →
  ♯ [ error , success ]′ (parseCommand (exec sum-cli) args)

  where

    error : String → _
    error = putStrLn ∘ String._++_ "*** Error: "

    sumNat : Maybe (List ℕ) → ℕ
    sumNat = maybe (foldr Nat._+_ 0) 0

    sumInt : Maybe (List ℤ) → ℤ
    sumInt = maybe (foldr Int._+_ (+ 0)) (+ 0)
    
    success : ParsedCommand (exec sum-cli) → IO _
    success ([                 ."sum"  ∷= _ & _ ])  = putStrLn "meh"
    success ([ ."int" [   z ]∙ ."exec" ∷= _ & vs ]) = putStrLn $ Int.show     $ sumInt vs
    success ([ ."nat" [ s z ]∙ ."exec" ∷= _ & vs ]) = putStrLn $ NatShow.show $ sumNat vs

    -- empty cases
    success ([ ."int" [      z   ]∙ _ [ () ]∙ _)
    success ([ ."nat" [ s    z   ]∙ _ [ () ]∙ _)
    success ([ _          [ s (s ()) ]∙ _)
