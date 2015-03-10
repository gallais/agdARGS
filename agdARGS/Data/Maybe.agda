module agdARGS.Data.Maybe where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Function

fromJust : ∀ {ℓ : Level} {A : Set ℓ} (a : Maybe A) {pr : maybe′ (const ⊤) ⊥ a} → A
fromJust (just a) = a
fromJust nothing {()}
