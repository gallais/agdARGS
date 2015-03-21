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
open import agdARGS.Data.Table as Table
open import agdARGS.System.Environment.Arguments
open import agdARGS.System.Console.CLI

files : _
files =
  record (lotsOf inj₂) { name        = "Files"
                       ; description = "List of text files to inspect" }

lines : _
lines =
  record flag { name        = "Lines"
              ; description = "Print the newline counts"
              ; flag        = "-l" }

words : _
words =
  record flag { name        = "Words"
              ; description = "Print the word counts"
              ; flag        = "-w" }

version : _
version =
  record flag { name        = "Version"
              ; description = "Output version information and exit"
              ; flag        = "--version" }

help : _
help =
  record flag { name        = "Help"
              ; description = "Display this help"
              ; flag        = "--help" }

cli : CLI
cli = record { default = just files
             ; options = lines `∷ words `∷ version `∷ help `∷ `[] }

record count : Set where
  field
    nb-words : ℕ
    nb-lines : ℕ
open count

FilePath = String

showCounts : List (FilePath × count) → String
showCounts xs =
  Table.show $ ("FilePath" ∷ "Lines" ∷ "Words" ∷ [])
             ∷ (Vec.fromList $ List.map showRow xs)
  where
    showRow : (FilePath × count) → Vec String 3
    showRow (fp , cnt) =
      let lws = nb-lines cnt ∷ nb-words cnt ∷ []
      in fp ∷ Vec.map NatShow.show lws

wc : List Char → count
wc = proj₁ ∘ List.foldl (uncurry cons) nil
  where
    cons : (C : count) (f : Bool) (c : Char) → Σ count (λ _ → Bool)
    cons C f ' '  = C , false
    cons C f '\t' = C , false
    cons C f '\n' = record C { nb-lines = 1 + nb-lines C } , false
    cons C f c    = (if f then C else record C { nb-words = 1 + nb-words C }) , true
    nil : count × Bool
    nil = record { nb-words = 0 ; nb-lines = 0 } , false

infix 5 _onFiniteFiles_
_onFiniteFiles_ : {A : Set} (f : String → A) → List FilePath → IO (List (FilePath × A))
f onFiniteFiles []         = return []
f onFiniteFiles (fp ∷ fps) =
  ♯ readFiniteFile fp        >>= λ content →
  ♯ (♯ (f onFiniteFiles fps) >>= λ rest    →
     ♯ return ((fp , f content) ∷ rest))

main : _
main = run $
  ♯ getArgs >>= λ args →
  ♯ [ error , success ]′ (parseArgs cli args)

  where

    error : String → _
    error = putStrLn ∘ (String._++_ "*** Error: ")

    treatFiles : List FilePath → _
    treatFiles fps =
      ♯ (wc ∘ String.toList onFiniteFiles fps) >>= λ counts →
      ♯ (putStrLn $ showCounts counts)

    success : CLValue cli (MaybeCLMode cli) → _
    success cliv =
           if is-just $ get "--help" cliv    then putStrLn $ usage (CLI.options cli)
      else if is-just $ get "--version" cliv then putStrLn "WordCount: version 0.1"
      else maybe′ treatFiles (error "No file provided") (CLValue.default cliv)