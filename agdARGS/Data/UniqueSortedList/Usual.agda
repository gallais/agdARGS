module agdARGS.Data.UniqueSortedList.Usual where

open import Data.String

open import agdARGS.Data.UniqueSortedList strictTotalOrder as USL public
open import agdARGS.Data.UniqueSortedList.SmartConstructors strictTotalOrder public
open USL.withEqDec _≟_ public