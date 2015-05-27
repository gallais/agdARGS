module agdARGS.Data.UniqueSortedList.Examples where

open import Data.String
open import agdARGS.Data.UniqueSortedList                   strictTotalOrder
open import agdARGS.Data.UniqueSortedList.SmartConstructors strictTotalOrder

Characteristics : UniqueSortedList _ _
Characteristics = "name" `∷ "age" `∷ "idcard" `∷ `[]
