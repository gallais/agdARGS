module System.Console.Argument where

open import Algebra.Bundles
open import Level using (0ℓ)
open import Data.Bool.Base using (Bool; false; true; if_then_else_)
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
open import Data.Product using (Σ)
open import Data.String.Base using (String)
open import Data.Sum.Base as Sum using (_⊎_)
open import Function.Base using (_$_; _∘_; id)

open import System.Console.Error

data Domain : Set₁ where
  Some : (S : Set)           → Domain
  ALot : (M : RawMagma 0ℓ 0ℓ) → Domain

Carrier : Domain → Set
Carrier (Some S) = S
Carrier (ALot M) = RawMagma.Carrier M

Parser : Set → Domain → Set
Parser e d = String → e ⊎ Carrier d

record Arguments : Set₁ where
  constructor mkArguments
  field
    required   : Bool
    domain     : Domain
    rawParser  : Parser String domain

parser : (arg : Arguments) → String → Error (Carrier $ Arguments.domain arg)
parser arg = fromSum ∘ Sum.map₁ couldNotParse ∘ Arguments.rawParser arg

ParsedArgumentsT : (Set → Set) → Arguments → Set
ParsedArgumentsT f args = f $ Carrier (Arguments.domain args)

update : (arg : Arguments) → ParsedArgumentsT Maybe arg →
         String → Error (ParsedArgumentsT Maybe arg)
update (mkArguments req (Some S) prs) (just val) str
  = throw tooManyArguments
update arg@(mkArguments req (Some S) prs) nothing str
  = just <$> parser arg str
update arg@(mkArguments req (ALot M) prs) mval str
  = do val′ ← parser arg str
       pure $ just $ let open RawMagma M in
                     maybe′ (_∙ val′) val′ mval

ParsedArguments : Arguments → Set
ParsedArguments args =
  ParsedArgumentsT (if Arguments.required args then id else Maybe) args

finalising :
  ErrorMsg → (args : Arguments) →
  ParsedArgumentsT Maybe args → Error (ParsedArguments args)
finalising err args val with Arguments.required args
... | false = pure val
finalising err args (just val) | true = pure val
finalising err args nothing    | true = throw err
