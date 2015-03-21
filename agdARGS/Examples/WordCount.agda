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
open import Data.List
open import Data.Char
open import Function
import agdARGS.Data.String as Str
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
  let (m , n , str) = foldl cons nil xs
  in Str.unlines $ reverse $ str m n

  where

    nil : ℕ × ℕ × (ℕ → ℕ → List String)
    nil = Str.length "FilePath" , Str.length "Lines" , λ m n →
          ("FilePath"                               String.++
           Str.replicate ((2 + m) ∸ Str.length "FilePath") ' ' String.++
           "Lines"                                             String.++
           Str.replicate ((2 + n) ∸ Str.length "Lines") ' '    String.++
           "Words") ∷ []

    cons : (ℕ × ℕ × (ℕ → ℕ → List String)) → FilePath × count → (ℕ × ℕ × (ℕ → ℕ → List String))
    cons (s₁ , s₂ , str) (fp , cnt) =
      let fp-length = Str.length fp
          `nb-lines = NatShow.show $ nb-lines cnt
          nb-length = Str.length `nb-lines
      in s₁ Nat.⊔ fp-length
       , s₂ Nat.⊔ nb-length
       , λ m n →
          (fp                                      String.++
           Str.replicate ((2 + m) ∸ fp-length) ' ' String.++
           `nb-lines                               String.++
           Str.replicate ((2 + n) ∸ nb-length) ' ' String.++
           NatShow.show (nb-words cnt))
           ∷ str m n

wc : List Char → count
wc = proj₁ ∘ foldl (uncurry cons) nil
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
      ♯ (wc ∘ toList onFiniteFiles fps) >>= λ counts →
      ♯ (putStrLn $ showCounts counts)

    success : CLValue cli (MaybeCLMode cli) → _
    success cliv =
           if is-just $ get "--help" cliv    then putStrLn $ usage (CLI.options cli)
      else if is-just $ get "--version" cliv then putStrLn "WordCount: version 0.1"
      else maybe′ treatFiles (error "No file provided") (CLValue.default cliv)