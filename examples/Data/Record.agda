module Data.Record where

open import Data.Char.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base
open import Data.String
open import Data.Record.DecPropositional _≟_

example : Record _ _ _ _
example = "string" ∷= "hello "
        < "lchars" ∷= 't' ∷ 'h' ∷ 'e' ∷ []
        < "vchars" ∷= toVec " world"
        < "char"   ∷= '!'
        < "record" ∷= "nested?"    ∷= 4
                    < "of course!" ∷= 'c'
                    < <>
        < <>

four : ℕ
four = example ∙ "record" ∙ "nested?"

the : List Char
the = example ∙ "lchars"
