module agdARGS.System.Console.Modifiers where

open import Level
open import Data.Unit
open import Data.String
open import Data.Product
open import Data.Maybe
open import Data.List
open import Data.String
open import Function
open import agdARGS.Algebra.Magma
open import agdARGS.Data.String
open import agdARGS.Data.Error as Error hiding (return)
open import agdARGS.Data.Record.Usual as RU public
open import agdARGS.System.Console.Options.Domain

Flag : (ℓ : Level) → Fields (suc ℓ) _
Flag ℓ = Type $ "description" ∷= Lift String
              ⟨ ⟨⟩

Option : (ℓ : Level) → Fields (suc ℓ) _
Option ℓ = Type $ "description" ∷= Lift String
                ⟨ "arguments"   ∷= Σ[ d ∈ Domain ℓ ] Parser d
                ⟨ ⟨⟩

data Modifier (ℓ : Level) (name : String) : Set (suc ℓ) where
  mkFlag    : Record _ (Flag ℓ)    → Modifier ℓ name
  mkOption  : Record _ (Option ℓ)  → Modifier ℓ name

flag : ∀ {ℓ name} → String → Modifier ℓ name
flag str = mkFlag $ "description" ∷= lift str ⟨ ⟨⟩

toFields : ∀ ℓ {lb ub} {names : UniqueSortedList lb ub} → Fields (suc ℓ) names
toFields ℓ = tabulate $ λ {s} → const (Modifier ℓ s)

Modifiers : ∀ ℓ → Set (suc ℓ)
Modifiers ℓ = Σ[ names ∈ USL ] Record names (toFields ℓ)

noModifiers : ∀ {ℓ} → Modifiers ℓ
noModifiers = , ⟨⟩

ParsedModifier : {ℓ : Level} {name : String} → Modifier ℓ name → Set ℓ
ParsedModifier (mkFlag f)   = Lift ⊤
ParsedModifier (mkOption o) = Carrier $ proj₁ $ `project "arguments" o

ParsedModifiers : ∀ {ℓ} {names : USL} (mods : Record names (toFields ℓ)) → Set ℓ
ParsedModifiers {names = names} mods =
  Record names (Maybe RU.[ Type $ RU.map (const ParsedModifier) mods ])


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
  go (nothing , ps) z      p = Error.return (just p , ps)
  go {mods = mkRecord (mod , mods)} (just q  , ps) {name} z p = (_, ps) <$>
    (case mod return (λ m → ParsedModifier m → ParsedModifier m → Error (Maybe (ParsedModifier m))) of λ
      { (mkFlag f)   → λ _ _ → throw $ concatList $ "MkFlag " ∷ name ∷ " set twice" ∷ []
      ; (mkOption o) →
        let dom = proj₁ $ `project "arguments" o
        in case dom return (λ d → Carrier d → Carrier d → Error (Maybe (Carrier d))) of λ
          { (Some _) → λ _ _ → throw $ concatList $ "MkOption " ∷ name ∷ " set twice" ∷ []
          ; (ALot m) → λ p q → Error.return (just (RawMagma._∙_ m p q))
          }
      }) p q
