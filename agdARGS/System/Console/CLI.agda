module agdARGS.System.Console.CLI where

open import Level
open import Data.Unit
open import Data.Maybe as Maybe
open import Data.List
open import Data.Sum as Sum
open import Data.Product
open import Data.String
open import Category.Monad
open import Function

open import agdARGS.System.Console.Options public
module Opts = Options zero
open Opts public

open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Options.Instances zero public
open import agdARGS.System.Console.Options.Usage     zero public

record CLI : Set₁ where
  field
    default : Maybe (Option zero)
    options : Options

record CLMode (cli : CLI) : Set₁ where
  field
    default : Option zero → Set
    options : Mode (CLI.options cli)

MaybeCLMode : (cli : CLI) → CLMode cli
MaybeCLMode cli =
  record { default = Maybe ∘ SetDomain ∘ Option.domain
         ; options = MaybeMode }

record CLValue (cli : CLI) (clm : CLMode cli) : Set₁ where
  field
    default : maybe (CLMode.default clm) (Lift ⊤) (CLI.default cli)
    options : Values (CLI.options cli) (CLMode.options clm)


parseArgs : (cli : CLI) → List String → String ⊎ CLValue cli (MaybeCLMode cli)
parseArgs cli strs =
  let res = parse strs (CLI.default cli) (CLI.options cli)
  in Sum.map id (uncurry $ λ def vals → record { default = def ; options = vals }) res

get : {cli : CLI} (str : String) (opts : CLValue cli (MaybeCLMode cli)) → _
get str = genericGet str ∘ CLValue.options
