module agdARGS.System.Console.CLI where

open import Level
open import Data.Unit
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

mutual

  record Command (ℓ : Level) : Set (suc ℓ) where
    inductive
    constructor mkCommand
    field
      description : String
      subcommands : SubCommands ℓ
      modifiers   : Modifiers ℓ
      arguments   : Arguments ℓ

  SubCommands : ∀ ℓ → Set (suc ℓ)
  SubCommands ℓ = ∃ (Commands ℓ)

  data Commands (ℓ : Level) (names : USL) : Set (suc ℓ) where
    commands : Record names (tabulate (const (Command ℓ))) → Commands ℓ names

basic : {ℓ : Level} → String → Arguments ℓ → Command ℓ
basic str args = mkCommand str (, commands ⟨⟩) (, ⟨⟩) args

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

{-
  data ParsedModifiers {ℓ : Level} {modNames : USL} (mods : Record modNames (toFields ℓ)) : Set ℓ where
    theModifiers : Record modNames (Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ]) → ParsedModifiers mods
-}

  ParsedModifiers : ∀ {ℓ} {names : USL} (mods : Record names (toFields ℓ)) → Set ℓ
  ParsedModifiers {names = names} mods =
    Record names (Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ])

  ParsedModifier : {ℓ : Level} {name : String} → Modifier ℓ name → Set ℓ
  ParsedModifier (flag f)   = Lift ⊤
  ParsedModifier (option o) = Carrier $ proj₁ $ `project "arguments" o

  ParsedArgument : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArgument (d , p) = Carrier d

  ParsedArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArguments (d , p) = Maybe $ Carrier d

infix  1 [_
infixr 2 _[_]∙_
infix  3 _∷=_&_]
pattern [_ p = p
pattern _∷=_&_] descr mods args = theCommand {descr} mods args
pattern _[_]∙_ desc pr sub     = subCommand {sub = desc} pr sub

open import agdARGS.Data.Error as Error renaming (return to ret)

updateModifier :
  {ℓ : Level} {names : USL} {mods : Record names (toFields ℓ)} (ps : ParsedModifiers mods) →
  {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
  Error (ParsedModifiers mods)
updateModifier {ℓ} ps pr p = mkRecord <$> go (content ps) pr p

  where

  go : {lb ub : _} {names : UniqueSortedList lb ub} {mods : Record names (toFields ℓ)} →
       let fs = fields $ Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ] in
       (ps : [Record] names fs) {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
       Error $ [Record] names fs
  go (q       , ps) (s pr) p = (λ ps → q , ps) <$> go ps pr p
  go (nothing , ps) z      p = ret (just p , ps)
  go {mods = mkRecord (mod , mods)} (just q  , ps) {name} z p = (_, ps) <$>
    (case mod return (λ m → ParsedModifier m → ParsedModifier m → Error (Maybe (ParsedModifier m))) of λ
      { (flag f)   → λ _ _ → throw $ concatList $ "Flag " ∷ name ∷ " set twice" ∷ []
      ; (option o) → 
        let dom = proj₁ $ `project "arguments" o
        in case dom return (λ d → Carrier d → Carrier d → Error (Maybe (Carrier d))) of λ
          { (Some _) → λ _ _ → throw $ concatList $ "Option " ∷ name ∷ " set twice" ∷ []
          ; (ALot m) → λ p q → ret (just (RawMagma._∙_ m p q))
          }
      }) p q


open import Data.Sum

updateArgument :
  {ℓ : Level} (d : Domain ℓ) (p : Parser d) (ps : ParsedArguments (d , p)) →
  String → Error $ ParsedArguments (d , p)
updateArgument (Some S) p ps x = throw "Too Many arguments: only one expected"
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
    ... | ALot m | parser = parser str >>= λ w → ret (just (v ∙ w))
      where open RawMagma m

[dummy] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub) {fs : [Fields] ℓ args} →
          [Record] args ([ Maybe [ fs ]])
[dummy] (_ ■)             = lift tt
[dummy] (_ UU., _ ∷ args) = nothing , [dummy] args

dummy : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args} →
        Record args (Maybe RU.[ fs ])
dummy = mkRecord $ [dummy] _

open import agdARGS.Relation.Nullary
open import agdARGS.Data.UniqueSortedList.Usual

parseModifier : {ℓ : Level} (c : Command ℓ) {x : String} (recyxs recxs : Error $ ParsedCommand c)
                (pr : x ∈ proj₁ (modifiers c)) → Error $ ParsedCommand c
parseModifier (mkCommand descr (subs , commands cs) mods args) {x} recyxs recxs pr = 
  (case (project′ pr (proj₂ $ mods)) return (λ m → Error (ParsedModifier m)) of λ
        { (flag f)   → inj₂ $ lift tt
        ; (option o) → proj₂ (`project "arguments" o) x
        })
  >>= λ p → recyxs >>= λ rec →
      case rec of λ
        { (theCommand mods args) → (λ m → theCommand m args) <$> updateModifier mods pr p
        ; (subCommand _ _)       → throw "Found a flag for command XXX with subcommand YYY" }

parseArgument : {ℓ : Level} (c : Command ℓ) (recyxs : String ⊎ ParsedCommand c)
                (x : String) → String ⊎ ParsedCommand c
parseArgument (mkCommand descr (sub , commands subs) mods (d , p)) recyxs x =
  recyxs >>= λ rec →
    case rec of λ
      { (theCommand mods args) → theCommand mods <$> updateArgument d p args x
      ; (subCommand _ _)       → throw "Found and argument for command XXX with subcommand YYY"
      }

