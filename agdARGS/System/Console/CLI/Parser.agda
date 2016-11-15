module agdARGS.System.Console.CLI.Parser where

open import Data.List
open import Data.String
open import Data.Sum
open import Data.Product
open import Data.Maybe
open import Function
open import agdARGS.Relation.Nullary

open import agdARGS.Data.Error
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.Data.Record.Usual
open import agdARGS.System.Console.CLI


mutual

  parseSubCommand : ∀ {ℓ} (c : Command ℓ) {x} → List String →
                    x ∈ proj₁ (subcommands c) → Error $ ParsedCommand c
  parseSubCommand (mkCommand _ (subs , commands cs) _ _) xs pr =
    (λ s → subCommand pr s) <$> parseCommand (project′ pr cs) xs

  parseCommand : ∀ {ℓ} (c : Command ℓ) → List String → Error $ ParsedCommand c
  parseCommand c []          = throw "Not enough arguments"
  parseCommand c ("--" ∷ xs) = theCommand dummy
                             <$> parseArguments (arguments c) xs nothing
  parseCommand c (x ∷ [])    =
    let dummyPD = inj₂ (theCommand dummy nothing) in
    dec (x ∈? proj₁ (subcommands c)) (parseSubCommand c []) $ λ _ →
    dec (x ∈? proj₁ (modifiers c)) (parseModifier c dummyPD dummyPD) $
    const $ parseArgument c dummyPD x
  parseCommand c (x ∷ y ∷ xs) =
    dec (x ∈? proj₁ (subcommands c)) (parseSubCommand c (y ∷ xs)) $ λ _ →
    let recyxs = parseCommand c (y ∷ xs)
        recxs  = parseCommand c xs
    in dec (x ∈? proj₁ (modifiers c)) (parseModifier c recyxs recxs) $ 
    const $ parseArgument c recyxs x
