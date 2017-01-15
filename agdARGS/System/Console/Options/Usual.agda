module agdARGS.System.Console.Options.Usual where

open import Level
open import Data.Nat using (ℕ)
open import agdARGS.Data.Nat.Read
open import Data.Integer using (ℤ)
open import agdARGS.Data.Integer.Read
open import Data.Empty
open import Data.Product
open import Data.String
open import Data.List
open import Function
open import Data.Sum
open import agdARGS.Algebra.Magma
open import agdARGS.Data.Error
open import agdARGS.System.Console.Options.Domain public

Arguments : (ℓ : Level) → Set (suc ℓ)
Arguments ℓ = Σ[ d ∈ Domain ℓ ] Parser d

none : ∀ {ℓ} → Arguments ℓ
none = Some (Lift ⊥) , const (throw "Argument provided when none expected")

lotsOf : ∀ {ℓ} → Arguments ℓ → Arguments ℓ
lotsOf {ℓ} (d , p) = ALot (List.rawMagma (Carrier d)) , ([_] <$>_) ∘ p

Regex = String

regex : Arguments zero
regex = Some Regex , inj₂

string : Arguments zero
string = Some String , inj₂

FilePath = String
filePath : Arguments zero
filePath = Some FilePath , inj₂

Regexp = String
regexp : Arguments zero
regexp = Some Regexp , inj₂

Url = String
url : Arguments zero
url = Some Url , inj₂

Nat : Arguments zero
Nat = Some ℕ , parseℕ

Int : Arguments zero
Int = Some ℤ , parseℤ
