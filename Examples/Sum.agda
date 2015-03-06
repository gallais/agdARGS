module agdARGS.Examples.Sum where

open import Level as Level
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Sum
open import Data.Nat
open import Data.Char
open import Data.String as Str
open import Data.List as List
open import Function

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

config : Arguments
config = version `∷ help `∷ `[]

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.Examples.Bindings.Arguments

main : _
main = run $
  ♯ getArgs >>= λ args →
  ♯ let vs = parse args (just nats) config in
    putStrLn $
      [ id
      , (uncurry $ λ ns opts →
           if      is-just $ get "--help" opts then usage config
           else if is-just $ get "-V" opts     then "Sum: version 0.9"
           else maybe (NatShow.show ∘ foldl _+_ 0) "0" ns)
      ]′ vs