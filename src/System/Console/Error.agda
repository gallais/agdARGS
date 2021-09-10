module System.Console.Error where

open import Level using (Level)
open import Data.List.Base as List using ([])
open import Data.List.NonEmpty using (List⁺; _∷_; _⁺++⁺_)
open import Data.Sum.Base using (_⊎_; [_,_]′)
open import Data.String.Base using (String; _++_)
open import Function.Base using (_∘′_)

private
  variable
    a b e : Level
    A : Set a
    B : Set b
    E : Set e

data ErrorMsg : Set where
  couldNotParse    : String → ErrorMsg
  missingOption    : String → ErrorMsg
  missingArgument  : ErrorMsg
  optionSetTwice   : String → ErrorMsg
  tooManyArguments : ErrorMsg
  missingOptArg    : String → ErrorMsg

errorMsg : ErrorMsg → String
errorMsg (couldNotParse str) = "Could not parse argument: " ++ str
errorMsg (missingOption str) = "Missing required modifier:" ++ str
errorMsg missingArgument     = "Missing required argument"
errorMsg (optionSetTwice nm) = "Option " ++ nm ++ " set twice"
errorMsg (tooManyArguments)  = "Too many arguments, only one expected"
errorMsg (missingOptArg nm)  = "Missing argument for option " ++ nm

data Error (A : Set a) : Set a where
  fail : List⁺ ErrorMsg → Error A
  pure : A → Error A

throw : ErrorMsg → Error A
throw msg = fail (msg ∷ [])

infixl 3 _<*>_
_<*>_ : Error (A → B) → Error A → Error B
pure f   <*> pure x   = pure (f x)
fail es₁ <*> fail es₂ = fail (es₁ ⁺++⁺ es₂)
fail es₁ <*> pure _   = fail es₁
pure _   <*> fail es₂ = fail es₂

infixr 4 _<$>_
_<$>_ : (A → B) → Error A → Error B
f <$> x = pure f <*> x

fromSum : ErrorMsg ⊎ A → Error A
fromSum = [ throw , pure ]′

infixr 2 _>>=_
_>>=_ : Error A → (A → Error B) → Error B
fail es >>= f = fail es
pure a  >>= f = f a
