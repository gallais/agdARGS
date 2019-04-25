module Data.Record where

open import Data.Char.Base
open import Data.Index
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
four = example ∙ "record" [ "of course!" ]∷= "hehe" ∙ "nested?"

the : List Char
the = example ∙ "lchars"

case : ∀ n → Index ("one" ∷ "two" ∷ "three" ∷ []) n → ℕ
case 0 [ "one"   ] = 10
case 1 [ "two"   ] = 11
case 2 [ "three" ] = 12
