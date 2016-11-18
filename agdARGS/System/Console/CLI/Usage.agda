module agdARGS.System.Console.CLI.Usage where

open import Level
open import Data.Nat
open import Data.Product
open import Data.List as List hiding (replicate)
open import Data.String as String hiding (unlines)
open import agdARGS.Data.String
open import Function

open import agdARGS.Data.UniqueSortedList.Usual as UU
open import agdARGS.Data.Record.Usual as RU
open import agdARGS.System.Console.CLI

Printer : Set
Printer = ℕ → List String -- indentation level

indent : ℕ → String → String
indent i str = replicate i ' ' String.++ str

open import agdARGS.System.Console.Modifiers

usageModifier : {ℓ : Level} (name : String) (cs : Modifier ℓ name) → Printer
usageModifier name mod i =
  (case mod of λ
    { (mkFlag f)   → indent i $ name String.++ indent 2 (lower $ `project "description" f)
    ; (mkOption o) → indent i $ name String.++ indent 2 (lower $ `project "description" o) })
  ∷ []

usageModifiers : ∀ {ℓ} {names : USL} → Record names (toFields ℓ) → Printer
usageModifiers = RU.foldr (λ _ mod p i → usageModifier _ mod i List.++ p i) (const [])

mutual

  usageCommand : ∀ {ℓ i} (name : String) (r : Command ℓ name {i}) → Printer
  usageCommand name r i =
              (indent i $ name String.++ indent 2 (description r))
            ∷ usageCommands (proj₂ $ subcommands r) (2 + i)
      List.++ usageModifiers (proj₂ $ modifiers r) (2 + i)


  usageCommands : ∀ {ℓ i} {names : USL} (cs : Commands ℓ names {i}) → Printer
  usageCommands (commands (mkRecord cs)) =
    RU.[foldr] (λ _ c p i → usageCommand _ c i List.++ p i) (const []) cs

usage : {ℓ : Level} (cli : CLI ℓ) → String
usage cli = unlines ∘ (_$ 0) ∘ usageCommand (name cli) $ exec cli
