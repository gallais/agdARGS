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

rawMagmaList : {ℓ : Level} (A : Set ℓ) → RawMagma ℓ
rawMagmaList A = record { Carrier = List A ; _∙_ = List._++_ }

parseDigit : Char → Maybe ℕ
parseDigit '0' = just 0
parseDigit '1' = just 1
parseDigit '2' = just 2
parseDigit '3' = just 3
parseDigit '4' = just 4
parseDigit '5' = just 5
parseDigit '6' = just 6
parseDigit '7' = just 7
parseDigit '8' = just 8
parseDigit '9' = just 9
parseDigit _   = nothing

parseNat : String → Maybe ℕ
parseNat = go ∘ reverse ∘ toList
  where
    go : List Char → Maybe ℕ
    go []       = nothing
    go (x ∷ []) = parseDigit x
    go (x ∷ xs) = 
      parseDigit x >>= λ d →
      go xs        >>= λ ds → return $ d + 10 * ds
      where open RawMonad Maybe.monad

nats : Argument Level.zero
nats = record { name        = "Nats"
              ; description = "Natural numbers to sum"
              ; flag        = ""
              ; optional    = false
              ; domain      = ALot (rawMagmaList ℕ)
              ; parser      = λ s → maybe′ (inj₂ ∘ [_]) (inj₁ $ "Invalid Natural Number: " Str.++ s) $ parseNat s
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
  ♯ let vs = parse args (just nats) (version , -∞<↑ _ ∷ ↑ _ <+∞ ■) in
    putStrLn $
      [ id
      , (λ { (ns , -V , _) →
           if is-just -V
           then "Sum: version 0.9"
           else maybe (NatShow.show ∘ foldl _+_ 0) "0" ns })
      ]′ vs
