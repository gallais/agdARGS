module Data.Singleton where

data Singleton {a} {A : Set a} : A → Set a where
  indeed : (a : A) → Singleton a
