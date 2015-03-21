module agdARGS.Data.String where

open import Level
open import Data.Nat
open import Data.Bool
open import Data.Sum
open import agdARGS.Data.Sum as Sum
open import Data.Char as Char
open import Data.String hiding (unlines)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)
import agdARGS.Data.List as List
open import lib.Nullary
open import Category.Monad
open import Function

fromVec : {n : ℕ} → Vec Char n → String
fromVec = fromList ∘ Vec.toList

concatList : List String → String
concatList = List.foldr _++_ ""

concatVec : {n : ℕ} → Vec String n → String
concatVec = Vec.foldr _ _++_ ""

unlines : List String → String
unlines = concatList ∘ List.intersperse "\n"

replicate : ℕ → Char → String
replicate n = fromList ∘ List.replicate n

length : String → ℕ
length = List.length ∘ toList

lines : String → List String
lines = List.map fromList ∘ List.breakOn isNewLine ∘ toList
  where
    isNewLine : Char → Bool
    isNewLine y = dec (y Char.≟ '\n') (const true) (const false)

parseAll : {ℓ : Level} {A : Set ℓ} (p : String → String ⊎ A) →
           List String → String ⊎ List A
parseAll p = List.foldl (λ res str → p str >>= (λ a → List._∷_ a <$> res)) (inj₂ List.[])
  where open RawMonad (Sum.monad String)
