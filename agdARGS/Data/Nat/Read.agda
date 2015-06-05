module agdARGS.Data.Nat.Read where

open import Data.Nat
open import Data.Char
open import Data.String as Str
open import Data.Sum
open import Data.Maybe as Maybe
open import Data.List
open import Category.Monad
open import Function
open import lib.Nullary
open import Relation.Nullary.Decidable using (True)

parseBase :
  (base : ℕ) {base≥2 : True (2 ≤? base)} {base≤16 : True (base ≤? 16)} →
  Char → Maybe ℕ
parseBase base c =
  parseDigit c >>= λ d → dec (suc d ≤? base) (const $ just d) (const nothing)
  where
    open RawMonad Maybe.monad

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
    parseDigit 'A' = just 10
    parseDigit 'B' = just 11
    parseDigit 'C' = just 12
    parseDigit 'D' = just 13
    parseDigit 'E' = just 14
    parseDigit 'F' = just 15
    parseDigit _   = nothing

parseℕ : String → String ⊎ ℕ
parseℕ str = maybe′ inj₂ failure $ goBase $ toList str

  where
    failure = inj₁ $ "Invalid Natural Number: " Str.++ str

    open RawMonad Maybe.monad

    go : (base : ℕ) {base≥2 : True (2 ≤? base)} {base≤16 : True (base ≤? 16)} → 
         List Char → Maybe ℕ
    go base {b2} {b16} = foldl step $ just 0
      where 
        step : Maybe ℕ → Char → Maybe ℕ
        step acc c = acc                         >>= λ ds →
                     parseBase base {b2} {b16} c >>= λ d →
                     return $ ds * base + d

    goBase : List Char → Maybe ℕ
    goBase ('0' ∷ 'x' ∷ xs) = go 16 xs
    goBase ('0' ∷ 'b' ∷ xs) = go 2  xs
    goBase xs               = go 10 xs


private

  test : _
  test = parseℕ "0bFF1"

