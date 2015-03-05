module agdARGS.Examples.Sum where

open import Level as Level
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Maybe as Maybe
open import Data.Sum
open import Data.Nat
open import Data.Char
open import Data.String as Str
open import Data.List as List
open import Function
open import Category.Monad

open import agdARGS.Data.Arguments
module Args = Arguments Level.zero
open Args

open import agdARGS.Algebra.Magma
open import agdARGS.Data.Nat.Read

nats : Argument Level.zero
nats = record { name        = "Nats"
              ; description = "Natural numbers to sum"
              ; flag        = ""
              ; optional    = false
              ; domain      = ALot (List.rawMagma ℕ)
              ; parser      = λ s → maybe′ (inj₂ ∘ [_]) (inj₁ $ "Invalid Natural Number: " Str.++ s) $ parseℕ s
              }

version : Argument Level.zero
version = record
            { name        = "Version"
            ; flag        = "-V"
            ; description = "Print the version number"
            ; optional    = true
            ; domain      = None
            ; parser      = lift tt }

open import IO
open import Coinduction
import Data.Nat.Show as NatShow
open import agdARGS.Examples.Bindings.Arguments
open import agdARGS.Data.Infinities

main : _
main = run $
  ♯ getArgs >>= λ args →
  ♯ let vs = parse args (just nats) config in
    putStrLn $
      [ id
      , (uncurry $ λ ns opts →
           if is-just $ get config "-V" opts
           then "Sum: version 0.9"
           else maybe (NatShow.show ∘ foldl _+_ 0) "0" ns)
      ]′ vs
  where
    config = version , -∞<↑ _ ∷ ↑ _ <+∞ ■