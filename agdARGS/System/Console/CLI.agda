module agdARGS.System.Console.CLI where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.String
open import agdARGS.Data.String as String
open import Data.Maybe

open import agdARGS.Data.UniqueSortedList.Usual as UU hiding (_,_∷_)
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

  Modifiers : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields (suc ℓ) args
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
  ParsedModifier (option o) = Carrier $ proj₁ $ `project "arguments" o

  ParsedArgument : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArgument (d , p) = Carrier d

  ParsedArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → Set ℓ
  ParsedArguments (d , p) = Maybe $ Carrier d


open import Data.Sum
open import agdARGS.Data.Sum as aDS
open import agdARGS.Algebra.Magma
open import Category.Monad

bindError : {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ} (eA :  String ⊎ A) (f : A → String ⊎ B) → String ⊎ B
bindError xs f = case xs of λ { (inj₁ err) → inj₁ err; (inj₂ a) → f a }

mapError : {ℓᵃ ℓᵇ : Level} {A : Set ℓᵃ} {B : Set ℓᵇ} (f : A → B) → String ⊎ A → String ⊎ B
mapError f xs = bindError xs (inj₂ ∘ f)

updateModifier :
  {ℓ : Level} {names : USL} {mods : Record names (Modifiers ℓ)} (ps : ParsedModifiers mods) →
  {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
  String ⊎ ParsedModifiers mods
updateModifier {ℓ} (theModifiers ps) pr p = mapError (theModifiers ∘ mkRecord) $ go (content ps) pr p

  where

  go : {lb ub : _} {names : UniqueSortedList lb ub} {mods : Record names (Modifiers ℓ)} →
       let fs = fields $ Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ] in
       (ps : [Record] names fs) {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
       String ⊎ [Record] names fs
  go (q       , ps) (s pr) p = mapError (λ ps → q , ps) $ go ps pr p
  go (nothing , ps) z      p = inj₂ (just p , ps)
  go {mods = mkRecord (mod , mods)} (just q  , ps) {name} z p = mapError (_, ps) $
    (case mod return (λ m → ParsedModifier m → ParsedModifier m → String ⊎ Maybe (ParsedModifier m)) of λ
      { (flag f)   → λ _ _ → inj₁ $ concatList $ "Flag " ∷ name ∷ " set twice" ∷ []
      ; (option o) → 
        let dom = proj₁ $ `project "arguments" o
        in case dom return (λ d → Carrier d → Carrier d → String ⊎ Maybe (Carrier d)) of λ
          { (Some _) → λ _ _ → inj₁ $ concatList $ "Option " ∷ name ∷ " set twice" ∷ []
          ; (ALot m) → λ p q → inj₂ (just (RawMagma._∙_ m p q))
          }
      }) p q

updateArgument :
  {ℓ : Level} (d : Domain ℓ) (p : Parser d) (ps : ParsedArguments (d , p)) →
  String → String ⊎ ParsedArguments (d , p)
updateArgument (Some S) p ps x = inj₁ $ "Too Many arguments: only one expected"
updateArgument (ALot M) p ps x = mapError (maybe′ (λ p q → just (RawMagma._∙_ M p q)) just ps) $ p x

parseArguments : {ℓ : Level} (p : Σ[ d ∈ Domain ℓ ] Parser d) → List String
                 → ParsedArguments p → String ⊎ ParsedArguments p
parseArguments p str dft = foldl (cons p) (inj₂ dft) str
  where
    open RawMonad (aDS.monad String)

    cons : (p : _) → String ⊎ ParsedArguments p → String → String ⊎ ParsedArguments p
    cons p (inj₁ str)      _   = inj₁ str
    cons p (inj₂ nothing)  str = just <$> proj₂ p str
    cons p (inj₂ (just v)) str with proj₁ p | proj₂ p
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

parseModifier : {ℓ : Level} (c : Command ℓ) {x : String} (recyxs recxs : String ⊎ ParsedCommand c)
                (pr : x ∈ proj₁ (modifiers c)) → String ⊎ ParsedCommand c
parseModifier (mkCommand descr (subs , commands cs) mods args) {x} recyxs recxs pr =
  bindError
      (case project′ pr (proj₂ $ mods) return (λ m → String ⊎ ParsedModifier m) of λ
        { (flag f)   → inj₂ $ lift tt
        ; (option o) → proj₂ (`project "arguments" o) x
        })
  $ λ p →
  bindError recyxs
  $ λ rec →
      case rec of λ
        { (theCommand mods args) → mapError (λ mods → theCommand mods args) $ updateModifier mods pr p
        ; (subCommand _ _)       → inj₁ "Found a flag for command XXX with subcommand YYY" }

parseArgument : {ℓ : Level} (c : Command ℓ) (recyxs : String ⊎ ParsedCommand c)
                (x : String) → String ⊎ ParsedCommand c
parseArgument (mkCommand descr (sub , commands subs) mods (d , p)) recyxs x =
  bindError recyxs
  $ λ rec →
    case rec of λ
      { (theCommand mods args) → mapError (theCommand mods) $ updateArgument d p args x
      ; (subCommand _ _)       → inj₁ "Found and argument for command XXX with subcommand YYY"
      }


mutual

  parseSubCommand : {ℓ : Level} (c : Command ℓ) {x : String} (xs : List String)
                    (pr : x ∈ proj₁ (subcommands c)) → String ⊎ ParsedCommand c
  parseSubCommand (mkCommand _ (subs , commands cs) _ _) xs pr =
    mapError (λ sub → subCommand pr sub) $ parseCommand (project′ pr cs) xs

  parseCommand : {ℓ : Level} (c : Command ℓ) → List String → String ⊎ ParsedCommand c
  parseCommand c []          = inj₁ "Not enough arguments"
  parseCommand c ("--" ∷ xs) = mapError (theCommand (theModifiers dummy)) $ parseArguments (arguments c) xs nothing
  parseCommand c (x ∷ [])     =
    let dummyPD = inj₂ (theCommand (theModifiers dummy) nothing) in
    dec (x ∈? proj₁ (subcommands c)) (parseSubCommand c []) $ λ _ →
    dec (x ∈? proj₁ (modifiers c)) (parseModifier c dummyPD dummyPD) (const $ parseArgument c dummyPD x)
  parseCommand c (x ∷ y ∷ xs) =
    dec (x ∈? proj₁ (subcommands c)) (parseSubCommand c (y ∷ xs)) $ λ _ →
      let recyxs = parseCommand c (y ∷ xs)
          recxs  = parseCommand c xs
      in
    dec (x ∈? proj₁ (modifiers c)) (parseModifier c recyxs recxs) (const $ parseArgument c recyxs x)