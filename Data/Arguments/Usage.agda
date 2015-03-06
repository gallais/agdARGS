open import Level using (Level)

module agdARGS.Data.Arguments.Usage (ℓ : Level) where

  open import agdARGS.Data.Arguments
  module Args = Arguments ℓ
  open Args
  open Argument

  open import Data.Nat
  open import Data.Product
  open import Data.Char
  open import Data.String as String hiding (unlines)
  open import Function

  open import Data.List as List using (List)
  import agdARGS.Data.List as List

  usage : Arguments → String
  usage args = let (n , f) = go args in
               unlines $ "Flags and Options:" List.∷ f n
    where
      unlines : List String → String
      unlines = List.foldr _++_ "" ∘ List.intersperse "\n"

      repeat : ℕ → Char → String
      repeat n = String.fromList ∘ List.repeat n

      length : String → ℕ
      length = List.length ∘ toList

      go : {lb ub : _} (args : UniqueSortedList lb ub) → ℕ × (ℕ → List String)
      go (lt ■)           = 0 , const List.[]
      go (hd , lt ∷ args) =
        let m       = length $ flag hd
            (n , f) = go args
            g n     = (flag hd ++ repeat (2 + n ∸ m) ' ' ++ description hd) List.∷ f n
        in (m ⊔ n , g)