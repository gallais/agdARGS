module System.Console.Command where

open import Level using (Level; suc; 0ℓ; _⊔_)

open import Data.List.Fresh using ([])
open import Data.Maybe.Base using (Maybe; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.String as String using (String)

open import Data.Record.NonDependent String String._≟_
  as Record
  using (Fields; IsField; theField; Record; mkRecord; _‼_)

open import System.Console.Error using (Error; missingArgument; pure; _<$>_; _<*>_)
open import System.Console.Modifier as Modifier using (Modifier; ParsedModifiersT; ParsedModifiers)
open import System.Console.Argument as Argument
  using (Arguments; ParsedArgumentsT; ParsedArguments; Some; ALot)

private
  variable
    ℓ : Level

record Command (nm : String) : Set₂ where
  inductive
  constructor mkCommand
  field
    description : String
    subcommands : Fields Command
    modifiers   : Fields Modifier
    arguments   : Arguments
open Command public

basic : {cmd : String} → (description : String) → Arguments → Command cmd
basic desc args = mkCommand desc [] [] args

data Any (p : (nm : String) → Command nm → Set ℓ)
         {nm : String} (cmd : Command nm) : Set (suc (suc 0ℓ) ⊔ ℓ) where
  here  : p nm cmd → Any p cmd
  there : {c : String} →
          (pos : IsField c (subcommands cmd)) →
          (sub : Any p (proj₂ (theField pos))) →
          Any p cmd

map : {p q : (nm : String) → Command nm → Set ℓ} ->
      (∀ nm cmd → p nm cmd → q nm cmd) →
      ∀ {nm} {cmd : Command nm} → Any p cmd → Any q cmd
map f (here pcmd)   = here (f _ _ pcmd)
map f (there pos p) = there pos (map f p)

module _ {f : ∀ {ℓ} → Set ℓ → Set ℓ}
       (pure : ∀ {a} {A : Set a} → A → f A)
       (_<*>_ : ∀ {a b} {A : Set a} {B : Set b} → f (A → B) → f A → f B)
       where

  traverse : {p q : (nm : String) → Command nm → Set ℓ} ->
             (∀ nm cmd → p nm cmd → f (q nm cmd)) →
             ∀ {nm} {cmd : Command nm} → Any p cmd → f (Any q cmd)
  traverse f (here pcmd)   = pure here <*> f _ _ pcmd
  traverse f (there pos p) = pure (there pos) <*> traverse f p

record ParsedCommandT
       (f g : Set → Set)
       (nm : String) (cmd : Command nm)
       : Set₂ where
  constructor mkParsedCommandT
  field
    modifiers : ParsedModifiersT f g (modifiers cmd)
    arguments : ParsedArgumentsT   g (arguments cmd)

module ParsedCommand where

  record ParsedCommand
         (nm : String) (cmd : Command nm)
         : Set₂ where
    constructor mkParsedCommand
    field
      modifiers : ParsedModifiers (modifiers cmd)
      arguments : ParsedArguments (arguments cmd)

  finalising : (nm : String) (cmd : Command nm) →
               ParsedCommandT Maybe Maybe nm cmd → Error (ParsedCommand nm cmd)
  finalising nm cmd (mkParsedCommandT ms as)
    = mkParsedCommand
      <$> Modifier.finalising ms
      <*> Argument.finalising missingArgument (arguments cmd) as

open ParsedCommand public using (ParsedCommand) hiding (module ParsedCommand)

ParseTreeT : (f g : Set → Set) {nm : String} (cmd : Command nm) → Set₂
ParseTreeT f g = Any (ParsedCommandT f g)

ParseTree : {nm : String} (cmd : Command nm) → Set₂
ParseTree = Any ParsedCommand

finalising : {f g : Set → Set} {nm : String} {cmd : Command nm} →
             ParseTreeT Maybe Maybe cmd → Error (ParseTree cmd)
finalising = traverse pure _<*>_ ParsedCommand.finalising

initParsedCommandT : {nm : String} {cmd : Command nm} → ParsedCommandT Maybe Maybe nm cmd
initParsedCommandT = mkParsedCommandT Modifier.initNothing nothing
