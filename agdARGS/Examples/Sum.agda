module agdARGS.Examples.Sum where

open import Level as Level
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import agdARGS.Data.Sum as Sum
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
  ♯ [ putStrLn ∘ String._++_ "*** Error: "
    , (λ cliv →
        if      is-just $ get "--help" cliv then putStrLn $ usage (CLI.options config)
        else if is-just $ get "-V"     cliv then putStrLn "Sum: version 0.9"
        else ♯ maybe′ readNatsFromFile (return $ validateNats $ default cliv) (get "-i" cliv) >>= λ ns →
             ♯ let sum = NatShow.show ∘ foldl _+_ 0 <$> ns in
               [ putStrLn ∘ String._++_ "*** Error: "
               , maybe′ writeFile putStrLn (get "-o" cliv) ]′ sum
       ) 
      ]′ (parseArgs config args)
  where
    open import Category.Monad
    open RawMonad (Sum.monad String) using (_<$>_)

    validateNats : Maybe (List ℕ) → String ⊎ List ℕ
    validateNats = maybe′ inj₂ (inj₁ "No Nat given")

    readNatsFromFile : String → IO (String ⊎ List ℕ)
    readNatsFromFile fp =
      ♯ readFiniteFile fp >>= λ str →
      ♯ return (parseAll parseℕ $ lines str)