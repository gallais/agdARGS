module agdARGS.System.Environment.Arguments.Primitive where

open import IO.Primitive
open import Data.List
open import Data.String

{-# FOREIGN GHC import qualified System.Environment #-}
{-# FOREIGN GHC import qualified Data.Text          #-}

postulate
  getArgs : IO (List String)

{-# COMPILE GHC getArgs = fmap Data.Text.pack <$> System.Environment.getArgs #-}
