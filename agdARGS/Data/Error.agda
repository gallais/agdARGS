module agdARGS.Data.Error where

open import Level
open import Data.Sum
open import Data.String
open import Function

Error : ∀ {ℓ} → Set ℓ → Set ℓ
Error = String ⊎_

throw : ∀ {ℓ} {A : Set ℓ} → String → Error A
throw = inj₁

return : ∀ {ℓ} {A : Set ℓ} → A → Error A
return = inj₂

infixr 0 _>>=_
_>>=_ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → Error A → (A → Error B) → Error B
inj₁ err >>= f = inj₁ err
inj₂ a   >>= f = f a

infixl 1 _<$>_
_<$>_ : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} → (A → B) → Error A → Error B
f <$> ma = ma >>= return ∘ f
