module agdARGS.System.Environment.Arguments where

open import Data.List
open import Data.String
open import IO
import agdARGS.System.Environment.Arguments.Primitive as Prim

getArgs : IO (List String)
getArgs = lift Prim.getArgs
