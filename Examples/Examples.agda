module agdARGS.Examples where

open import Level
open import Data.Bool
open import Data.String
open import Data.Maybe
open import Function

open import agdARGS.Data.Arguments
module Args = Arguments zero
open Args

open import agdARGS.Data.Infinities
open import Data.List as List
open import Data.Unit
open import Data.Empty

open import Relation.Nullary

inverse : Argument zero
inverse = record
            { name        = "Inverse"
            ; flag        = "-i"
            ; description = "Unmatched lines are considered matched and conversely"
            ; optional    = true
            ; domain      = None
            ; parser      = lift tt
            }

version : Argument zero
version = record
            { name        = "Version"
            ; flag        = "-V"
            ; description = "Print the version number"
            ; optional    = true
            ; domain      = None
            ; parser      = lift tt }

rawMagmaList : {ℓ : Level} (A : Set ℓ) → RawMagma ℓ
rawMagmaList A = record { Carrier = List A ; _∙_ = List._++_ }

textFiles : Argument zero
textFiles = record
              { name        = "Text Files"
              ; description = "Files to be dealt with"
              ; flag        = "-f"
              ; optional    = false
              ; domain      = ALot (rawMagmaList String)
              ; parser      = λ s → just (List.[ s ])
              }

fromJust : ∀ {ℓ : Level} {A : Set ℓ} (a : Maybe A) {pr : maybe′ (const ⊤) ⊥ a} → A
fromJust (just a) = a
fromJust nothing {()}

test : Arguments
test = fromJust $ Args.fromList $ textFiles ∷ version ∷ inverse ∷ []

testArg : Dec _
testArg = findArgument "-i" test