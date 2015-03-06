module agdARGS.Data.List where

open import Level using (Level)
open import Data.Bool
open import Data.Product
open import Data.List
open import Function

init : {ℓ : Level} {A : Set ℓ} (xs : List A) → List A
init []       = []
init (x ∷ []) = []
init (x ∷ xs) = x ∷ init xs

breakOn : {ℓ : Level} {A : Set ℓ} (P? : A → Bool) (xs : List A) → List (List A)
breakOn {A = A} P? xs =
  let (hd , tl) = foldr step ([] , []) xs
  in (if null hd then id else _∷_ hd) tl
  where

    step : A → (List A × List (List A)) → (List A × List (List A))
    step a (xs , xss) = if (P? a) then [] , xs ∷ xss else a ∷ xs , xss
