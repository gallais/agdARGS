module agdARGS.System.Console.CLI where

open import Level
open import Size
open import Data.Unit
open import Data.Bool
open import Data.Empty
open import Data.Product
open import Data.String
open import agdARGS.Algebra.Magma using (module RawMagma)
open import agdARGS.Data.String as String
open import Data.Maybe

open import agdARGS.Data.UniqueSortedList.Usual as UU hiding (_,_∷_)
open import agdARGS.Data.Record.Usual as RU

open import agdARGS.System.Console.Options.Domain
open import agdARGS.System.Console.Options.Usual
open import agdARGS.System.Console.Modifiers
open import Function

ParsedArgument : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
ParsedArgument (d , p) = Carrier d

ParsedArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
ParsedArguments (d , p) = Maybe $ Carrier d

infix 4 commands_
mutual

  record Command (ℓ : Level) (name : String) {i : Size} : Set (suc ℓ) where
    inductive
    constructor mkCommand
    field
      description : String
      subcommands : SubCommands ℓ {i}
      modifiers   : Modifiers ℓ
      arguments   : Arguments ℓ

  SubCommands : ∀ ℓ {i : Size} → Set (suc ℓ)
  SubCommands ℓ {i} = ∃ λ names → Commands ℓ names {i}

  data Commands (ℓ : Level) (names : USL) : {i : Size} → Set (suc ℓ) where
    commands_ : ∀ {i} → Record names (tabulate (λ {s} _ → Command ℓ s {i})) → Commands ℓ names {↑ i}

noSubCommands : ∀ {ℓ} → SubCommands ℓ
noSubCommands = , commands ⟨⟩

infix 4 commandsSugar
commandsSugar : ∀ {ℓ names} → Record names _ → Commands ℓ names
commandsSugar = commands_
syntax commandsSugar t = < t

basic : {ℓ : Level} {s : String} → Arguments ℓ → Command ℓ s
basic {s = str} args = mkCommand str (, commands ⟨⟩) (, ⟨⟩) args

record CLI (ℓ : Level) : Set (suc ℓ) where
  field
    name : String
    exec : Command ℓ name
open CLI public
open Command public

open import Data.List
open import agdARGS.Data.Infinities
open import agdARGS.Data.Record.Properties strictTotalOrder
open import Relation.Binary.PropositionalEquality

mutual

  data ParsedCommand {ℓ s} : (c : Command ℓ s) → Set (suc ℓ) where
    theCommand : {descr : String}
                 {subs : Σ[ names ∈ USL ] Commands ℓ names}
                 {modNames : USL} {mods : Record modNames (toFields ℓ)}
                 (parsedMods : ParsedModifiers mods)
                 {args : Σ[ d ∈ Domain ℓ ] Parser d}
                 (parsedArgs : ParsedArguments args)
                 → ParsedCommand (mkCommand descr subs (modNames , mods) args)

    subCommand : {descr : String}
                 {sub : String} {subs : USL} (pr : sub ∈ subs) {cs : Record subs _}
                 {mods : Σ[ names ∈ USL ] Record names (toFields ℓ)} →
                 (parsedSub : ParsedCommand (project′ pr cs))
                 {args : Σ[ d ∈ Domain ℓ ] Parser d}
                 → ParsedCommand (mkCommand descr (subs , commands cs) mods args)

ParsedInterface : ∀ {ℓ} → CLI ℓ → Set (suc ℓ)
ParsedInterface i = ParsedCommand (exec i)

infix  1 [_
infixr 2 _[_]∙_
infix  3 _∷=_&_]
pattern [_ p = p
pattern _∷=_&_] descr mods args = theCommand {descr} mods args
pattern _[_]∙_ desc pr sub     = subCommand {sub = desc} pr sub

open import agdARGS.Data.Error as Error hiding (return)
open import Data.Sum

updateArgument :
  {ℓ : Level} (d : Domain ℓ) (p : Parser d) (ps : ParsedArguments (d , p)) →
  String → Error $ ParsedArguments (d , p)
updateArgument (Some S) p (just _) _ = throw "Too Many arguments: only one expected"
updateArgument (Some S) p nothing x = just <$> p x
updateArgument (ALot M) p ps x = maybe′ (λ p q → just (RawMagma._∙_ M p q)) just ps <$> p x

parseArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → List String
                 → ParsedArguments p → Error $ ParsedArguments p
parseArguments p str dft = foldl (cons p) (inj₂ dft) str
  where

    cons : (p : _) → Error (ParsedArguments p) → String → Error (ParsedArguments p)
    cons p (inj₁ str)      _   = inj₁ str
    cons p (inj₂ nothing)  str = just <$> proj₂ p str
    cons p (inj₂ (just v)) str with proj₁ p | proj₂ p
    ... | Some _ | _      = inj₁ "Too many arguments: only one expected"
    ... | ALot m | parser = parser str >>= λ w → Error.return (just (v ∙ w))
      where open RawMagma m

[dummy] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
          (mods : Record args (tabulate (λ {s} _ → Modifier ℓ s))) →
          [Record] args (fields $ Type $ RU.map (const ParsedModifier) mods)
[dummy] (_ ■)             m                   = lift tt
[dummy] (_ UU., _ ∷ args) (mkRecord (mkFlag _   , ms)) = lift false , [dummy] args (mkRecord ms)
[dummy] (_ UU., _ ∷ args) (mkRecord (mkOption _ , ms)) = nothing    , [dummy] args (mkRecord ms)

dummy : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {mods : Record args (toFields ℓ)} →
        Record args (Type $ RU.map (const ParsedModifier) mods)
dummy = mkRecord $ [dummy] _ _

open import agdARGS.Relation.Nullary
open import agdARGS.Data.UniqueSortedList.Usual

parseModifier : ∀ {ℓ s} (c : Command ℓ s) {x : String} (recyxs recxs : Error (ParsedCommand c))
                → x ∈ proj₁ (modifiers c) → Error $ ParsedCommand c
parseModifier (mkCommand descr (subs , commands cs) mods args) {x} recyxs recxs pr = 
  (case (project′ pr (proj₂ $ mods)) return (λ m → Error (ParsedModifier m)) of λ
        { (mkFlag f)   → Error.return $ lift true
        ; (mkOption o) → just <$> proj₂ (`project "arguments" o) x
        })
  >>= λ p → recyxs >>= λ rec →
      case rec of λ
        { (theCommand mods args) → (λ m → theCommand m args) <$> updateModifier mods pr p
        ; (subCommand _ _)       → throw "Found a mkFlag for command XXX with subcommand YYY" }

parseArgument : ∀ {ℓ s} (c : Command ℓ s) → Error (ParsedCommand c) →
                String → Error $ ParsedCommand c
parseArgument (mkCommand descr (sub , commands subs) mods (d , p)) recyxs x =
  recyxs >>= λ rec →
    case rec of λ
      { (theCommand mods args) → theCommand mods <$> updateArgument d p args x
      ; (subCommand _ _)       → throw "Found and argument for command XXX with subcommand YYY"
      }
