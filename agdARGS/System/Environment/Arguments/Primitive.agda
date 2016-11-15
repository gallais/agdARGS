module agdARGS.System.Environment.Arguments.Primitive where

open import IO.Primitive
open import Data.List
open import Data.String

{-# IMPORT System.Environment #-}
{-# IMPORT Data.Text          #-}

postulate
  getArgs : IO (List String)

{-# COMPILED getArgs (fmap Data.Text.pack <$> System.Environment.getArgs) #-}
