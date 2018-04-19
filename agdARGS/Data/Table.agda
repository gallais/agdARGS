module agdARGS.Data.Table where

open import Level using (Level)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.List as List using (List ; _∷_ ; [])
open import Data.Vec as Vec hiding (zipWith ; _⊛_)
import Data.Vec.Categorical as Vec
open import Data.String as Str hiding (show)
open import agdARGS.Data.String as String
open import Function
open import Category.Functor
open import Category.Applicative

Table : (m n : ℕ) {ℓ : Level} (A : Set ℓ) → Set ℓ
Table m n A = Vec (Vec A n) m

infixr 3 _∥_
_∥_ : {m n p : ℕ} {ℓ : Level} {A : Set ℓ} → Table m n A → Table m p A → Table m (n + p) A
xs ∥ ys = Vec.zipWith Vec._++_ xs ys

functor : {m n : ℕ} {ℓ : Level} → RawFunctor (Table m n {ℓ})
functor = record { _<$>_ = map ∘ map }

infixl 3 _⊛_
_⊛_ : {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ}
      {m n : ℕ} (fs : Table m n (A → B)) (as : Table m n A) → Table m n B
fs ⊛ as = map Vec._⊛_ fs Vec.⊛ as

applicative : {m n : ℕ} {ℓ : Level} → RawApplicative (Table m n {ℓ})
applicative {m} {n} {ℓ}=
  record { pure = VecM.pure ∘ VecN.pure
         ; _⊛_  = _⊛_ }
  where
    module VecM = RawApplicative (Vec.applicative {ℓ} {m})
    module VecN = RawApplicative (Vec.applicative {ℓ} {n})

zipWith : {ℓᵃ ℓᵇ ℓᶜ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ} {C : Set ℓᶜ}
          {m n : ℕ} (f : A → B → C) → Table m n A → Table m n B → Table m n C
zipWith f ta tb = RawApplicative.pure applicative f ⊛ ta ⊛ tb

show : {m n : ℕ} → Table m n String → String
show {n = n} tb = String.unlines $ uncurry (flip _$_) res
  where
    P : Set
    P = Vec ℕ n × (Vec ℕ n → List String)

    showCell : String → ℕ → String
    showCell str n = str Str.++ (fromVec $ Vec.replicate {n = (2 + n) ∸ length str} ' ')

    cons : {m : ℕ} → Vec String n → P → P
    cons row (ms , str) =
      let strs-lengths   = Vec.map String.length row
          ns             = Vec.zipWith _⊔_ ms strs-lengths
      in ns , λ ls → (concatVec $ Vec.zipWith showCell row ls) ∷ str ls

    res : P
    res = foldr (const P) (λ {m} → cons {m}) (Vec.replicate 0 , const []) tb

