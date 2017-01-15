module agdARGS.Examples.Git where

open import agdARGS.System.Console.CLI.Examples
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.CLI.Usage
open import Function
open import IO

main = withCLI git $ const $ putStrLn $ usage git
