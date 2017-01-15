module agdARGS.Examples.Echo where

open import IO
open import Data.Maybe
open import Function
open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.Options.Usual
open import agdARGS.System.Console.Modifiers

echo : CLI _
echo = record
  { name = "echo"
  ; exec = record
  { description  = "Repeat its argument"
  ; subcommands  = noSubCommands
  ; arguments    = string
  ; modifiers    = noModifiers
  }
  }

main = withCLI echo handler where

  handler : ParsedInterface echo → _
  handler (theCommand _  a) = putStrLn (maybe id "" a)
  handler (subCommand () _)
