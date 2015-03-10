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

open import agdARGS.Data.Arguments
module Args = Arguments Level.zero
open Args
open import agdARGS.Data.Arguments.Instances Level.zero
open import agdARGS.Data.Arguments.Usage     Level.zero

open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read

nats : Argument Level.zero
nats = record (lotsOf parseℕ) { name = "Nats" ; description = "Natural numbers to sum" }

version : Argument Level.zero
version = record flag { name = "Version" ; flag = "-V" ; description = "Print the version number" }

help : Argument Level.zero
help = record flag { name = "Help" ; flag = "--help" ; description = "Print this help" }

input : Argument Level.zero
input = record (option inj₂) { name = "Input" ; flag = "-i" ; description = "Read nats from a file" }

output : Argument Level.zero
output = record (option inj₂) { name = "Output" ; flag = "-o" ; description = "Output sum to a file" }

config : Arguments
config = version `∷ input `∷ help `∷ output `∷ `[]

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.Examples.Bindings.Arguments

main : _
main = run $
  ♯ getArgs >>= λ args →
  ♯ [ putStrLn ∘ String._++_ "*** Error: "
    , (uncurry $ λ ns opts →
        if      is-just $ get "--help" opts then putStrLn $ usage config
        else if is-just $ get "-V" opts     then putStrLn "Sum: version 0.9"
        else ♯ maybe′ readNatsFromFile (return $ validateNats ns) (get "-i" opts) >>= λ ns →
             ♯ let sum = NatShow.show ∘ foldl _+_ 0 <$> ns in
               [ putStrLn ∘ String._++_ "*** Error: "
               , maybe′ writeFile putStrLn (get "-o" opts) ]′ sum
        )
      ]′ (parse args (just nats) config)
  where
    open import Category.Monad
    open RawMonad (Sum.monad String) using (_<$>_)

    validateNats : Maybe (List ℕ) → String ⊎ List ℕ
    validateNats = maybe′ inj₂ (inj₁ "No Nat given")

    readNatsFromFile : String → IO (String ⊎ List ℕ)
    readNatsFromFile fp =
      ♯ readFiniteFile fp >>= λ str →
      ♯ return (parseAll parseℕ $ lines str)