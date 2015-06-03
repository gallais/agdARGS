open import Level
open import Relation.Binary

module agdARGS.Data.UniqueSortedList.SmartConstructors
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

  open import agdARGS.Data.Maybe
  open import agdARGS.Data.Infinities
  open import agdARGS.Data.UniqueSortedList STO

  USL : Set (ℓʳ ⊔ ℓᵃ)
  USL = UniqueSortedList -∞ +∞

  `[] : USL
  `[] = -∞<+∞ ■

  infixr 5 _`∷_
  _`∷_ : ∀ x (xs : USL) {pr : _} → USL
  (x `∷ xs) {pr} = fromJust (insert x (-∞<↑ x) ↑ x <+∞ xs) {pr}

  infix 6 `[_]
  `[_] : ∀ x → USL
  `[ x ] = x `∷ `[]