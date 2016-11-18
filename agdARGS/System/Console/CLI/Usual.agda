module agdARGS.System.Console.CLI.Usual where

open import Level
open import IO
open import Data.Unit
open import Data.Sum
open import Data.String
open import Coinduction
open import Function

open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Parser
open import agdARGS.System.Environment.Arguments

error : String → IO _
error = putStrLn ∘ ("*** Error: " ++_)

withCLI : ∀ {ℓ} (c : CLI ℓ) (k : ParsedCommand (exec c) → IO ⊤) → _
withCLI c k = run $
  ♯ getArgs >>= λ args → ♯ [ error , k ]′ (parseInterface c args)
