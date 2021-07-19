module Stdlib where

open import Level

open import Data.Bool.Base using (true; false)
open import Relation.Nullary.Reflects using (of)
open import Relation.Nullary using (Dec; _because_)
open import Relation.Nullary.Decidable as Dec using (True)

open import Function.Base using (id)

private
  variable
    a b : Level

lift? : {P : Set a} → (P? : Dec P) → Dec (Lift b P)
lift? = Dec.map′ Level.lift Level.lower

true? : {P : Set a} → (P? : Dec P) → Dec (True P?)
Dec.does  (true? d) = Dec.does d
Dec.proof (true? (true  because proof)) = of _
Dec.proof (true? (false because proof)) = of id

open import Relation.Nary
open import Function.Nary.NonDependent
open import Data.Nat.Base

⌊_⌋? : ∀ {n ls r} {as : Sets n ls} {R : as ⇉ Set r}
       (R? : Decidable R) → Decidable {as = as} ⌊ R? ⌋
⌊_⌋? {zero}  R? = lift? (true? R?)
⌊_⌋? {suc n} R? = λ x → ⌊_⌋? {n} (R? x)
