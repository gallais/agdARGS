module agdARGS.Examples.Examples where

open import Level
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.String
open import Data.Maybe
open import agdARGS.Data.Maybe
open import Function

open import agdARGS.Data.Arguments
module Args = Arguments zero
open Args

open import agdARGS.Data.Infinities
open import Data.List as List
open import Data.Unit
open import Data.Empty

open import Relation.Nullary
open import agdARGS.Algebra.Magma

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

textFiles : Argument zero
textFiles = record
              { name        = "Text Files"
              ; description = "Files to be dealt with"
              ; flag        = "-f"
              ; optional    = false
              ; domain      = ALot (List.rawMagma String)
              ; parser      = λ s → inj₂ (List.[ s ])
              }

test : Arguments
test = version `∷ inverse `∷ `[]

testArg : Dec _
testArg = findArgument "-i" test

testParse : List (String ⊎ _)
testParse = List.map (λ xs → parse xs (just textFiles) test) tests
  where
    parse₁ = "-i" ∷ "Filename.txt" ∷ "-V" ∷ "otherFileName.html" ∷ []
    parse₂ = "Filename.txt" ∷ "-V" ∷ "otherFileName.html" ∷ []
    parse₃ = "-V" ∷ []
    tests  = parse₁ ∷ parse₂ ∷ parse₃ ∷ []


