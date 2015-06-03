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

git : Record _ (Command zero)
git = "description" ∷= lift "A distributed revision control system with an emphasis on speed,\
                            \ data integrity, and support for distributed, non-linear workflows"
    ⟨ "modifiers"   ∷= "add" `∷ "clone" `∷ `[ "push" ] , git-modifiers
    ⟨ "arguments"   ∷= ALot (List.rawMagma String) , inj₁
    ⟨ ⟨⟩ where

  git-modifiers : Record _ (Modifiers zero)
  git-modifiers = "add"   ∷= command git-add
                ⟨ "clone" ∷= command git-clone
                ⟨ "push"  ∷= command git-push
                ⟨ ⟨⟩ where

    git-add : Record _ (Command zero)
    git-add = "description" ∷= lift "Add file contents to the index"
            ⟨ "modifiers"   ∷= `[] , ⟨⟩
            ⟨ "arguments"   ∷= ALot (List.rawMagma String) , inj₁
            ⟨ ⟨⟩

    git-clone : Record _ (Command zero)
    git-clone = "description" ∷= lift "Clone a repository into a new directory"
              ⟨ "modifiers"   ∷= `[] , ⟨⟩
              ⟨ "arguments"   ∷= Some String , inj₁
              ⟨ ⟨⟩

    git-push : Record _ (Command zero)
    git-push = "description" ∷= lift "Update remote refs along with associated objects"
             ⟨ "modifiers"   ∷= `[ "--force" ] , "--force" ∷= flag force ⟨ ⟨⟩
             ⟨ "arguments"   ∷= None , lift tt
             ⟨ ⟨⟩ where

      force : Record _ (Flag zero)
      force = "description" ∷= lift "Usually, the command refuses to update a remote ref that\
                               \ is not an ancestor of the local ref used to overwrite it. This\
                               \ flag disables the check. This can cause the remote repository\
                               \ to lose commits; use it with care."
            ⟨ ⟨⟩