module agdARGS.Data.Record.Usual where

open import Data.String

open import agdARGS.Data.UniqueSortedList.Usual                           public
open import agdARGS.Data.Record                   strictTotalOrder as Rec public
open import agdARGS.Data.Record.SmartConstructors strictTotalOrder as SC
  hiding (module withEqDec) public
open SC.withEqDec _≟_ public
