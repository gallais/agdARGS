module agdARGS.Data.Nat.Read where

open import Data.Nat
open import Data.Char
open import Data.String as Str
open import Data.Sum
open import Data.Maybe as Maybe
open import Data.List
open import Category.Monad
open import Function

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

parseℕ : String → String ⊎ ℕ
parseℕ str = maybe′ inj₂ failure $ go $ reverse $ toList str
  where
    failure = inj₁ $ "Invalid Natural Number: " Str.++ str

    go : List Char → Maybe ℕ
    go []       = just 0
    go (x ∷ []) = parseDigit x
    go (x ∷ xs) = 
      parseDigit x >>= λ d →
      go xs        >>= λ ds → return $ d + 10 * ds
      where open RawMonad Maybe.monad