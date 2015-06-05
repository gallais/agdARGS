module agdARGS.Data.Integer.Read where

open import Data.Char
open import Data.String as String
open import Data.Sum as Sum
open import Data.List
open import Function

open import Data.Nat
open import Data.Integer
open import agdARGS.Data.Nat.Read

parseℤ : String → String ⊎ ℤ
parseℤ z = [ const failure , inj₂ ]′ $ go $ toList z where

  failure : String ⊎ ℤ
  failure = inj₁ $ "Invalid Integer: " String.++ z

  go : List Char → String ⊎ ℤ
  go ('-' ∷ n) = Sum.map id (0 ⊖_) $ parseℕ $ fromList n
  go n         = Sum.map id (+_)   $ parseℕ z

