module System.Console.Modifiers where

open import Data.Bool.Base using (Bool; false)
open import Data.List.Fresh using (_∷#_; [])
open import Data.List.Fresh.Relation.Unary.All using (_∷_; [])
open import Data.Product using (_,_; proj₂)
open import Data.String as String using (String)
open import Function.Base using (const; _$_)

open import Data.Default
open import Data.Record.NonDependent String String._≟_

pattern _≔_ a b = a , b

Flag : Fields (const Set)
Flag = "description" ≔ String
    ∷# "default"     ≔ Bool
    ∷# []

Option : Fields (const Set)
Option = "description" ≔ String
      ∷# "arguments"   ≔ {!!}
      ∷# []

data Modifier (nm : String) : Set₁ where
  mkFlag   : Record proj₂ Flag → Modifier nm
  mkOption : Record proj₂ Option → Modifier nm

flag : {nm : String} →
       (description : String) →
       {{flag : WithDefault false}} →
       Modifier nm
flag desc {{flag}} = mkFlag $ mkRecord $ desc ∷ flag .value ∷ []

{-

open import Level
open import Data.Unit
open import Data.Bool
open import Data.String
open import Data.Product
open import Data.Maybe
open import Data.List
open import Data.String
open import Function
open import agdARGS.Algebra.Monoid
open import agdARGS.Data.String
open import agdARGS.Data.Error as Error hiding (return)
open import agdARGS.Data.Record.Usual as RU public
open import agdARGS.System.Console.Options.Domain

toFields : ∀ ℓ {lb ub} {names : UniqueSortedList lb ub} → Fields (suc ℓ) names
toFields ℓ = RU.tabulate $ λ {s} → const (Modifier ℓ s)

Modifiers : ∀ ℓ → Set (suc ℓ)
Modifiers ℓ = Σ[ names ∈ USL ] Record names (toFields ℓ)

noModifiers : ∀ {ℓ} → Modifiers ℓ
noModifiers = , ⟨⟩

ParsedModifier : {ℓ : Level} {name : String} → Modifier ℓ name → Set ℓ
ParsedModifier (mkFlag f)   = Lift Bool
ParsedModifier (mkOption o) = Maybe (Carrier $ proj₁ $ `project "arguments" o)

ParsedModifiers : ∀ {ℓ} {names : USL} (mods : Record names (toFields ℓ)) → Set ℓ
ParsedModifiers {names = names} mods =
  Record names (Type $ RU.map (const ParsedModifier) mods)

updateModifier :
  {ℓ : Level} {names : USL} {mods : Record names (toFields ℓ)} (ps : ParsedModifiers mods) →
  {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
  Error (ParsedModifiers mods)
updateModifier {ℓ} ps pr p = mkRecord <$> go (content ps) pr p

  where

  go : {lb ub : _} {names : UniqueSortedList lb ub} {mods : Record names (toFields ℓ)} →
       let fs = fields $ (Type $ RU.map (const ParsedModifier) mods) in
       (ps : [Record] names fs) {name : String} (pr : name ∈ names) (p : ParsedModifier (project′ pr mods)) →
       Error $ [Record] names fs
  go (q , ps) (s pr) p = (λ ps → q , ps) <$> go ps pr p
  go {mods = mkRecord (mkFlag _ , _)}   (q , ps) z p = Error.return (p , ps)
  go {mods = mkRecord (mkOption _ , _)} (nothing , ps) z p = Error.return (p , ps)
  go {mods = mkRecord (mkOption o , _)} (just q  , ps) {name} z p =  (_, ps) <$>
        let dom = proj₁ $ `project "arguments" o
        in (case dom return (λ d → Maybe (Carrier d) → Carrier d → Error (Maybe (Carrier d))) of λ
          { (Some _) → λ _ _ → throw $ concatList $ "MkOption " ∷ name ∷ " set twice" ∷ []
          ; (ALot m) → λ p q → Error.return $ let open RawMonoid (fromMagma m) in p ∙ just q
          }) p q
-}
