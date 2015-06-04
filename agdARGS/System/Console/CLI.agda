module agdARGS.System.Console.CLI where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.String
open import Data.Maybe

open import agdARGS.Data.UniqueSortedList.Usual as UU
open import agdARGS.Data.Record.Usual as RU

open import agdARGS.System.Console.Options.Domain
open import Function

mutual

  record Command (ℓ : Level) : Set (suc ℓ) where
    inductive
    constructor mkCommand
    field
      description : String
      subcommands : Σ[ names ∈ USL ] Commands ℓ names
      modifiers   : Σ[ names ∈ USL ] Record names (Modifiers ℓ)
      arguments   : Σ[ d ∈ Domain ℓ ] Parser d

  data Commands (ℓ : Level) (names : USL) : Set (suc ℓ) where
    commands : Record names (tabulate (const (Command ℓ))) → Commands ℓ names

  Flag : (ℓ : Level) → Fields (suc ℓ) `[ "description" ]
  Flag ℓ = Type $ "description" ∷= Lift String
                ⟨ ⟨⟩

  Option : (ℓ : Level) → Fields (suc ℓ) ("description" `∷ `[ "arguments" ])
  Option ℓ = Type $ "description" ∷= Lift String
                  ⟨ "arguments"   ∷= Σ[ d ∈ Domain ℓ ] Parser d
                  ⟨ ⟨⟩

  data Modifier (ℓ : Level) (name : String) : Set (suc ℓ) where
    flag    : Record _ (Flag ℓ)    → Modifier ℓ name
    option  : Record _ (Option ℓ)  → Modifier ℓ name

  Modifiers : (ℓ : Level) {args : USL} → Fields (suc ℓ) args
  Modifiers ℓ = tabulate $ λ {s} → const (Modifier ℓ s)

record CLI (ℓ : Level) : Set (suc ℓ) where
  field
    name : String
    exec : Command ℓ
open CLI public
open Command public

open import Data.List
open import agdARGS.Data.Infinities
open import agdARGS.Data.Record.Properties strictTotalOrder
open import Relation.Binary.PropositionalEquality

mutual

  data ParsedCommand {ℓ : Level} : (c : Command ℓ) → Set (suc ℓ) where
    theCommand : {descr : String}
                 {subs : Σ[ names ∈ USL ] Commands ℓ names}
                 {modNames : USL} {mods : Record modNames (Modifiers ℓ)}
                 (parsedMods : ParsedModifiers mods)
                 {args : Σ[ d ∈ Domain ℓ ] Parser d}
                 (parsedArgs : ParsedArguments args)
                 → ParsedCommand (mkCommand descr subs (modNames , mods) args)

    subCommand : {descr : String}
                 {sub : String} {subs : USL} (pr : sub ∈ subs) {cs : Record subs _}
                 {mods : Σ[ names ∈ USL ] Record names (Modifiers ℓ)} →
                 (parsedSub : ParsedCommand (project′ pr cs))
                 {args : Σ[ d ∈ Domain ℓ ] Parser d}
                 → ParsedCommand (mkCommand descr (subs , commands cs) mods args)


  data ParsedModifiers {ℓ : Level} {modNames : USL} (mods : Record modNames (Modifiers ℓ)) : Set ℓ where
    theModifiers : Record modNames (Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ]) → ParsedModifiers mods

  ParsedModifier : {ℓ : Level} {name : String} → Modifier ℓ name → Set ℓ
  ParsedModifier (flag f)   = Lift ⊤
  ParsedModifier (option o) = maybe id (Lift ⊤) ∘ Carrier $ proj₁ $ `project "arguments" o

  ParsedArgument : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArgument (d , p) = maybe id (Lift ⊥) (Carrier d)

  ParsedArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArguments (d , p) = Maybe $ maybe id (Lift ⊥) (Carrier d)


open import Data.Sum
open import agdARGS.Data.Sum as aDS
open import agdARGS.Algebra.Magma
open import Category.Monad

parseArgument : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → String → String ⊎ ParsedArgument p
parseArgument (d , p) str with Carrier d
... | nothing = inj₁ "Argument when none was expected"
... | just v  = p str

parseArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → List String
                 → ParsedArguments p → String ⊎ ParsedArguments p
parseArguments p str dft = foldl (cons p) (inj₂ dft) str
  where
    open RawMonad (aDS.monad String)

    cons : (p : _) → String ⊎ ParsedArguments p → String → String ⊎ ParsedArguments p
    cons p (inj₁ str)      _   = inj₁ str
    cons p (inj₂ nothing)  str = just <$> parseArgument p str
    cons p (inj₂ (just v)) str with proj₁ p | proj₂ p
    ... | None   | _      = ⊥-elim $ lower v
    ... | Some _ | _      = inj₁ "Too many arguments: only one expect"
    ... | ALot m | parser = parser str >>= λ w → return (just (v ∙ w))
      where open RawMagma m

[dummy] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub) {fs : [Fields] ℓ args} →
          [Record] args ([ Maybe [ fs ]])
[dummy] (_ ■)             = lift tt
[dummy] (_ UU., _ ∷ args) = nothing , [dummy] args

dummy : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args} →
        Record args (Maybe RU.[ fs ])
dummy = mkRecord $ [dummy] _

open import lib.Nullary
open import agdARGS.Data.UniqueSortedList.Usual

mutual

  parseSubCommand : {ℓ : Level} (c : Command ℓ) {x : String} (xs : List String)
                    (pr : x ∈ proj₁ (subcommands c)) → String ⊎ ParsedCommand c
  parseSubCommand (mkCommand _ (subs , commands cs) _ _) xs pr =
    case parseCommand (project′ pr cs) xs of λ
           { (inj₁ err) → inj₁ err
           ; (inj₂ sub) → inj₂ (subCommand pr sub) }

  parseModifier : {ℓ : Level} (c : Command ℓ) {x : String} (recyxs recxs : String ⊎ ParsedCommand c)
                  (pr : x ∈ proj₁ (modifiers c)) → String ⊎ ParsedCommand c
  parseModifier c recyxs recxs pr =
        case project′ pr (proj₂ $ modifiers c) of λ
          { (flag f)   → case recyxs of λ { (inj₁ err) → inj₁ err ; (inj₂ c) → {!!} }
          ; (option o) → {!!} }

  parseCommand : {ℓ : Level} (c : Command ℓ) → List String → String ⊎ ParsedCommand c
  parseCommand c []          = inj₁ "Not enough arguments"
  parseCommand c ("--" ∷ xs) =
    case parseArguments (arguments c) xs nothing of λ
      { (inj₁ err)  → inj₁ err
      ; (inj₂ args) → inj₂ $ theCommand (theModifiers dummy) args }
  parseCommand c (x ∷ [])     = inj₁ "todo: implement"
  parseCommand c (x ∷ y ∷ xs) =
    dec (x ∈? proj₁ (subcommands c)) (parseSubCommand c (y ∷ xs)) $ λ _ →
      let recyxs = parseCommand c (y ∷ xs)
          recxs  = parseCommand c xs
      in
    dec (x ∈? proj₁ (modifiers c)) (parseModifier c recyxs recxs) $ λ _ →
    case parseArgument (arguments c) x of {!!}
