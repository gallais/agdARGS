open import Level using (Level)

module agdARGS.System.Console.Options.Usage (ℓ : Level) where

  open import agdARGS.System.Console.Options
  private module Opts = Options ℓ
  open Opts
  open Option

  open import Data.Nat
  open import Data.Product
  open import Data.Char
  open import Data.String as String hiding (unlines)
  open import agdARGS.Data.String
  open import Function

  open import Data.List as List using (List)
  import agdARGS.Data.List as List

  usage : Options → String
  usage args = let (n , f) = go args in
               unlines $ "Flags and Options:" List.∷ f n
    where

      go : {lb ub : _} (args : UniqueSortedList lb ub) → ℕ × (ℕ → List String)
      go (lt ■)           = 0 , const List.[]
      go (hd , lt ∷ args) =
        let m       = length $ flag hd
            (n , f) = go args
            g n     = ("  " ++ flag hd ++ replicate (2 + n ∸ m) ' ' ++ name hd ++ ": " ++ description hd)
                      List.∷ f n
        in (m ⊔ n , g)