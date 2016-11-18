module agdARGS.Examples.WordCount where

open import Level
open import Coinduction
open import IO
open import Data.Bool
open import Data.Nat as Nat
open import Data.Nat.Show as NatShow
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.String as String
open import Data.Vec as Vec hiding (_>>=_)
open import Data.List as List
open import Data.Char
open import Function
import agdARGS.Data.String as Str
open import agdARGS.Data.Error using (Error)
open import agdARGS.Data.Table as Table
open import agdARGS.System.Environment.Arguments
open import agdARGS.System.Console.CLI
open import agdARGS.System.Console.CLI.Usual
open import agdARGS.System.Console.Modifiers
open import agdARGS.System.Console.Options.Usual

open import agdARGS.Data.Record.Usual as RU hiding (_∷=_⟨_)

WordCount : Command _ "WordCount"
WordCount = record
  { description = "Print newline, and word counts for each file"
  ; subcommands = noSubCommands
  ; modifiers   = , "-l"        ∷= flag "Print the newline count"
                  ⟨ "-w"        ∷= flag "Print the word count"
                  ⟨ "--help"    ∷= flag "Display this help"
                  ⟨ "--version" ∷= flag "Output version information and exit"
                  ⟨ ⟨⟩
  ; arguments   = lotsOf filePath }

cli : CLI Level.zero
cli = record
  { name = "WordCount"
  ; exec = WordCount }

record count : Set where
  field
    nb-words : ℕ
    nb-lines : ℕ
open count

count0 : count
nb-words count0 = 0
nb-lines count0 = 0

_∙_ : count → count → count
nb-words (c ∙ d) = (_+_ on nb-words) c d
nb-lines (c ∙ d) = (_+_ on nb-lines) c d

showCounts : ParsedModifiers (proj₂ (modifiers WordCount)) →
             List (FilePath × count) → String
showCounts mods xs =
  -- Lines (resp. Words) are counted if the -l (resp. -w) flag is set
  -- or none at all are set.
  let keepLines = is-just (mods ‼ "-l") ∨ is-nothing (mods ‼ "-w")
      keepWords = is-just (mods ‼ "-w") ∨ is-nothing (mods ‼ "-l")
      total     = List.foldr (_∙_ ∘ proj₂) count0 xs
      xs        = xs List.∷ʳ ("Total" , total)
  in Table.show $ showCol true      "FilePath" proj₁                             xs
                ∥ showCol keepLines "Lines"    (NatShow.show ∘ nb-lines ∘ proj₂) xs
                ∥ showCol keepWords "Words"    (NatShow.show ∘ nb-words ∘ proj₂) xs
    where
      showCol : (b : Bool) (str : String) (f : (FilePath × count) → String) →
                (xs : List (FilePath × count)) →
                Table (Nat.suc $ List.length xs) (if b then 1 else 0) String
      showCol true  str f xs = (str ∷ []) ∷ Vec.map (Vec.[_] ∘ f) (Vec.fromList xs)
      showCol false str f xs = []         ∷ Vec.map (const [])    (Vec.fromList xs)

wc : List Char → count
wc = proj₁ ∘ List.foldl (uncurry cons) nil
  where
    cons : (C : count) (f : Bool) (c : Char) → Σ count (λ _ → Bool)
    cons C f ' '  = C , false
    cons C f '\t' = C , false
    cons C f '\n' = record C { nb-lines = 1 + nb-lines C } , false
    cons C f c    = (if f then C else record C { nb-words = 1 + nb-words C }) , true
    nil : count × Bool
    nil = count0 , false

infix 5 _onFiniteFiles_
_onFiniteFiles_ : {A : Set} (f : String → A) → List FilePath → IO (List (FilePath × A))
f onFiniteFiles []         = return []
f onFiniteFiles (fp ∷ fps) =
  ♯ readFiniteFile fp        >>= λ content →
  ♯ (♯ (f onFiniteFiles fps) >>= λ rest    →
     ♯ return ((fp , f content) ∷ rest))

main : _
main = withCLI cli success where

  treatFiles : ParsedModifiers (proj₂ (modifiers WordCount)) → List FilePath → IO _
  treatFiles opts fps =
    ♯ (wc ∘ String.toList onFiniteFiles fps) >>= λ counts →
    ♯ (putStrLn $ showCounts opts counts)

  success : ParsedInterface cli → IO _
  success (theCommand mods args) =
         if is-just (mods ‼ "--version") then putStrLn "WordCount: version 0.1"
    else if is-just (mods ‼ "--help")    then putStrLn "TODO: usage"
    else maybe (treatFiles mods) (error "No file provided") args
  success (subCommand () _)
