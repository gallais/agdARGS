module System.Console.Command.Parser where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; foldl)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (proj₂)
open import Data.String as String using (String)

open import Data.Record.NonDependent String String._≟_
  as Record
  using (IsField; theField; isField?; _‼_)

open import Function.Base using (id; _$_; case_of_)

open import Relation.Nullary

open import System.Console.Argument as Argument
open import System.Console.Command
open import System.Console.Error
open import System.Console.Modifier as Modifier

parseArguments : (args : Arguments) → ParsedArgumentsT Maybe args →
                 List String → Error (ParsedArgumentsT Maybe args)
parseArguments args old = foldl (λ u s → u >>= λ acc → Argument.update args acc s) (pure old)

parseCommand : {nm : String} (cmd : Command nm) → List String →
               ParsedCommandT Maybe Maybe nm cmd →
               Error (ParsedCommandT Maybe Maybe nm cmd)

parseModifier : {nm mod : String} (cmd : Command nm) →
                (pos : IsField mod (modifiers cmd)) →
                List String →
                ParsedCommandT Maybe Maybe nm cmd →
                (factory : ParsedModifierT id id (proj₂ (theField pos)) →
                           Error (ParsedModifiersT Maybe Maybe (modifiers cmd))) →
                Error (ParsedCommandT Maybe Maybe nm cmd)

parseCommand cmd []          old = pure old
parseCommand cmd ("--" ∷ xs) old
  = do args ← parseArguments (arguments cmd) (arguments old) xs
       pure $ record old { arguments = args }
parseCommand cmd (arg  ∷ xs) old
  = case isField? arg (modifiers cmd) of λ where
      (yes pos) → parseModifier cmd pos xs old (Modifier.update (modifiers old) pos)
      (no _)    → do args ← Argument.update (arguments cmd) (arguments old) arg
                     parseCommand cmd xs (record old { arguments = args })

parseModifier {mod = mod} cmd pos rest old factory with proj₂ (theField pos)
... | mkFlag   flg = do mods ← factory true
                        parseCommand cmd rest (record old { modifiers = mods })
... | mkOption opt = case rest of λ where
                       []       → throw (missingOptArg mod)
                       (x ∷ xs) → do arg ← parser (opt ‼ "arguments") x
                                     mods ← factory arg
                                     parseCommand cmd xs (record old { modifiers = mods })

parse : {nm : String} (cmd : Command nm) → List String → Error (ParseTreeT Maybe Maybe cmd)
parse cmd []            = pure (here initParsedCommandT)
parse cmd xs@("--" ∷ _) = here <$> parseCommand cmd xs initParsedCommandT
parse cmd ys@(x ∷ xs)
  = case isField? x (subcommands cmd) of λ where
      (yes pos) → there pos <$> parse (proj₂ $ theField pos) xs
      (no _)    → here <$> parseCommand cmd ys initParsedCommandT
