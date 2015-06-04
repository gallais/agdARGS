module agdARGS.System.Console.CLI.Examples where

open import Level
open import Data.Unit
open import Data.String
open import Data.Product
open import Data.Sum

open import agdARGS.Data.Record.Usual
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.CLI
open import agdARGS.Algebra.Magma

open import Function

git-exec : Record _ (Command zero)
git-exec = "description" ∷= lift "A distributed revision control system with an emphasis on speed,\
                                 \ data integrity, and support for distributed, non-linear workflows"
         ⟨ "subcommands" ∷= "add" `∷ "clone" `∷ `[ "push" ] , git-modifiers
         ⟨ "modifiers"   ∷= `[] , ⟨⟩
         ⟨ "arguments"   ∷= ALot (List.rawMagma String) , inj₁
         ⟨ ⟨⟩ where

  git-modifiers : Commands zero _
  git-modifiers =
    commands $ "add"   ∷= git-add
             ⟨ "clone" ∷= git-clone
             ⟨ "push"  ∷= git-push
             ⟨ ⟨⟩ where

    git-add : Record _ (Command zero)
    git-add = "description" ∷= lift "Add file contents to the index"
            ⟨ "subcommands" ∷= `[] , commands ⟨⟩
            ⟨ "modifiers"   ∷= `[] , ⟨⟩
            ⟨ "arguments"   ∷= ALot (List.rawMagma String) , inj₁
            ⟨ ⟨⟩

    git-clone : Record _ (Command zero)
    git-clone = "description" ∷= lift "Clone a repository into a new directory"
              ⟨ "subcommands" ∷= `[] , commands ⟨⟩
              ⟨ "modifiers"   ∷= `[] , ⟨⟩
              ⟨ "arguments"   ∷= Some String , inj₁
              ⟨ ⟨⟩

    git-push : Record _ (Command zero)
    git-push = "description" ∷= lift "Update remote refs along with associated objects"
             ⟨ "subcommands" ∷= `[] , commands ⟨⟩
             ⟨ "modifiers"   ∷= `[ "--force" ] , "--force" ∷= flag force ⟨ ⟨⟩
             ⟨ "arguments"   ∷= None , lift tt
             ⟨ ⟨⟩ where

      force : Record _ (Flag zero)
      force = "description" ∷= lift "Usually, the command refuses to update a remote ref that\
                               \ is not an ancestor of the local ref used to overwrite it. This\
                               \ flag disables the check. This can cause the remote repository\
                               \ to lose commits; use it with care."
            ⟨ ⟨⟩

git : CLI zero
git = record { name = "git" ; exec = git-exec }

open import agdARGS.System.Console.CLI.Usage

test : String
test = usage git

