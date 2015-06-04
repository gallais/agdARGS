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

pad


mutual

  {-# TERMINATING #-}
  usageCommand : {ℓ : Level} (name : String) (r : Record _ (Command ℓ)) → Printer
  usageCommand name r i =
              (indent i $ name String.++ indent 2 (lower $ `project "description" r))
            ∷ usageCommands (proj₂ $ `project "subcommands" r) (2 + i)
      List.++ usageModifiers (proj₂ $ `project "modifiers" r)  (2 + i)

  usageModifier : {ℓ : Level} (name : String) (cs : Modifier ℓ name) → Printer
  usageModifier name mod i =
    (case mod of λ
      { (flag f)   → indent i $ name String.++ indent 2 (lower $ `project "description" f)
      ; (option o) → indent i $ name String.++ indent 2 (lower $ `project "description" o) })
    ∷ []

  usageModifiers : {ℓ : Level} {names : USL} (cs : Record names (Modifiers ℓ)) → Printer
  usageModifiers cs = go _ (content cs) ∘ (2 +_) where
    go : {ℓ : Level} {lb ub : _} (names : UniqueSortedList lb ub)
         (cs : [Record] names ([tabulate] names $ λ {s} → const (Modifier ℓ s))) → Printer
    go (_ ■)               cs       i = []
    go (arg UU., _ ∷ args) (c , cs) i = usageModifier arg c i List.++  go args cs i


  usageCommands : {ℓ : Level} {names : USL} (cs : Commands ℓ names) → Printer
  usageCommands (commands cs) = go _ (content cs) ∘ (2 +_) where
    go : {ℓ : Level} {lb ub : _} (names : UniqueSortedList lb ub)
         (cs : [Record] names ([tabulate] _ (const (Record _ (Command ℓ))))) → ℕ → List String
    go (_ ■)               cs       i = []
    go (arg UU., _ ∷ args) (c , cs) i = usageCommand arg c i List.++ go args cs i

usage : {ℓ : Level} (cli : CLI ℓ) → String
usage cli = unlines ∘ (_$ 0) ∘ usageCommand (name cli) $ exec cli
