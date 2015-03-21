module agdARGS.Examples.Sum where

open import Level as Level
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Sum as Sum
open import Data.Nat
open import Data.String as String
open import agdARGS.Data.String as Str
open import Data.List as List
import agdARGS.Data.List as List
open import Function
open import lib.Nullary


open import agdARGS.System.Console.CLI

open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read

nats : Option Level.zero
nats = record (lotsOf parseℕ) { name = "Nats" ; description = "Natural numbers to sum" }

version : Option Level.zero
version = record flag { name = "Version" ; flag = "-V" ; description = "Print the version number" }

help : Option Level.zero
help = record flag { name = "Help" ; flag = "--help" ; description = "Print this help" }

input : Option Level.zero
input = record (option inj₂) { name = "Input" ; flag = "-i" ; description = "Read nats from a file" }

output : Option Level.zero
output = record (option inj₂) { name = "Output" ; flag = "-o" ; description = "Output sum to a file" }

config : CLI
config = record { default = just nats
                ; options = version `∷ input `∷ help `∷ output `∷ `[] }
open CLValue

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.System.Environment.Arguments

main : _
main = run $
  ♯ getArgs >>= λ args →
  ♯ [ error , success ]′ (parseArgs config args)

  where

    error : String → _
    error = putStrLn ∘ String._++_ "*** Error: "

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