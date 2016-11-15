module agdARGS.Data.UniqueSortedList.Examples where

open import Data.String
open import agdARGS.Data.UniqueSortedList                   strictTotalOrder
open import agdARGS.Data.UniqueSortedList.SmartConstructors strictTotalOrder

Characteristics : USL
Characteristics = let open MayFail in "name" `∷ "age" `∷ "idcard" `∷ `[]

Characteristics′ : USL
Characteristics′ = let open NeverFail in "name" `∷ "age" `∷ "idcard" `∷ `[]
