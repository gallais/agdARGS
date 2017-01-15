module agdARGS.Algebra.Monoid where

open import Level
open import Data.Maybe
open import agdARGS.Algebra.Magma

record RawMonoid (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    ε       : Carrier
    _∙_     : Carrier → Carrier → Carrier

fromMagma : ∀ {ℓ} → RawMagma ℓ → RawMonoid ℓ
fromMagma mg = record { Carrier = Maybe (RawMagma.Carrier mg) ; ε = nothing ; _∙_ = product }
  module FromMagma where
    product : Maybe _ → Maybe _ → Maybe _
    product x nothing = x
    product nothing y = y
    product (just x) (just y) = just (RawMagma._∙_ mg x y)
