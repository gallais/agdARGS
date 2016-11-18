module agdARGS.System.Console.CLI.Examples where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.String
open import Data.Product
open import Data.List
open import Data.Sum

open import agdARGS.Data.Record.Usual
open import agdARGS.Data.UniqueSortedList.Usual
open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Options.Usual
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.Algebra.Magma

open import Function

git-exec : Command zero "git"
git-exec = record
 { description = "A distributed revision control system with an emphasis on speed,\
                 \ data integrity, and support for distributed, non-linear workflows"
 ; subcommands = , < "add"   ∷= record (basic $ lotsOf filePath) { description = "Add file contents to the index" }
                   ⟨ "clone" ∷= record (basic url) { description = "Clone a repository into a new directory" }
                   ⟨ "push"  ∷= git-push
                   ⟨ ⟨⟩
 ; modifiers   = noModifiers
 ; arguments   = lotsOf filePath } where

  git-push = record
    { description = "Update remote refs along with associated objects"
    ; subcommands = noSubCommands
    ; modifiers   = , "--force" ∷= flag $ "Usually, the command refuses to update a remote ref that\
                                        \ is not an ancestor of the local ref used to overwrite it. This\
                                        \ flag disables the check. This can cause the remote repository\
                                        \ to lose commits; use it with care."
                    ⟨ ⟨⟩
    ; arguments   = none
    }

git : CLI zero
git = record { name = "git" ; exec = git-exec }
