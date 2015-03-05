module agdARGS.Algebra.Magma where

open import Level

record RawMagma (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    _∙_     : Carrier → Carrier → Carrier

module List where

  open import Data.List

  rawMagma : {ℓ : Level} (A : Set ℓ) → RawMagma ℓ
  rawMagma A = record { Carrier = List A ; _∙_ = _++_ }

module String where

  open import Data.String

  rawMagma : RawMagma zero
  rawMagma = record { Carrier = String ; _∙_ = _++_ }

module Unit where

  open import Data.Unit
  open import Function

  rawMagma : RawMagma zero
  rawMagma = record { Carrier = ⊤ ; _∙_ = const $ const tt }
