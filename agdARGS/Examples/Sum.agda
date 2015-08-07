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
open import lib.Nullary


open import agdARGS.System.Console.CLI

open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read
open import agdARGS.Data.Integer.Read
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.Data.Record.Usual
open import agdARGS.System.Console.Options.Domain

sum-nat : Command Level.zero
sum-nat = record { description = "exec"
                 ; subcommands = `[] , commands ⟨⟩
                 ; modifiers   = `[] , ⟨⟩
                 ; arguments   = ALot (List.rawMagma ℕ) , mapError [_] ∘ parseℕ
                 }

sum-int : Command Level.zero
sum-int = record { description = "exec"
                 ; subcommands = `[] , commands ⟨⟩
                 ; modifiers   = `[] , ⟨⟩
                 ; arguments   = ALot (List.rawMagma ℤ) , mapError [_] ∘ parseℤ
                 }


sum-cli : CLI Level.zero
sum-cli = record { name = "sum"
                 ; exec = sum-exec } where

  sum-exec : Command Level.zero
  sum-exec = record { description = "sum"
                    ; subcommands = "nat" `∷ `[ "int" ] , sum-exec-subs
                    ; modifiers   = `[] , ⟨⟩
                    ; arguments   = Some (Lift ⊥) , λ _ → inj₁ "Argument provided when none expected"
                    } where

    sum-exec-subs : Commands Level.zero _
    sum-exec-subs = commands $ "nat" ∷= sum-nat
                             ⟨ "int" ∷= sum-int
                             ⟨ ⟨⟩

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.System.Environment.Arguments

main : _
main = run $
  ♯ getArgs >>= λ args →
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

{-
    getNats : CLValue config (MaybeCLMode config) → IO (String ⊎ List ℕ)
    getNats clv = maybe′ readNatsFromFile (return $ validateNats $ default clv) $ get "-i" clv
      where
        readNatsFromFile : String → IO (String ⊎ List ℕ)
        readNatsFromFile fp =
          ♯ readFiniteFile fp >>= λ str →
          ♯ return (parseAll parseℕ $ lines str)

        validateNats : Maybe (List ℕ) → String ⊎ List ℕ
        validateNats = maybe′ inj₂ (inj₁ "No Nat given")

    putNats : CLValue config (MaybeCLMode config) → ℕ → IO _
    putNats clv = maybe′ writeFile putStrLn (get "-o" clv) ∘ NatShow.show

    success : CLValue config (MaybeCLMode config) → _
    success clv =
           if is-just $ get "--help" clv then putStrLn $ usage (CLI.options config)
      else if is-just $ get "-V"     clv then putStrLn "Sum: version 0.9"
      else ♯ getNats clv >>= λ ns → ♯ [ error , putNats clv ∘ foldl _+_ 0 ]′ ns
-}
