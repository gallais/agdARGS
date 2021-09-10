module System.Console.Modifier where

open import Level using (Level; Lift; lift)
open import Algebra.Bundles using (RawMagma)
open import Data.Bool.Base using (Bool; false)
open import Data.Default
open import Data.List.Fresh using (_∷#_; [])
open import Data.List.Fresh.Relation.Unary.All as All using (All; _∷_; [])
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any)
open import Data.Maybe.Base using (Maybe; nothing; just; fromMaybe)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Sum.Base as Sum using (inj₂)
open import Function.Base using (const; _$_; id; flip)

open import Data.Record.NonDependent String String._≟_
  as Record
  using (Fields; Record; mkRecord; _‼_)

open import System.Console.Error
open import System.Console.Argument as Argument
  using (Arguments; ParsedArgumentsT; ParsedArguments; Some; ALot)

private
  variable
    ℓ : Level
    nm : String

pattern _≔_ a b = a , b

Flag : Fields (const Set)
Flag = "description" ≔ String
    ∷# "default"     ≔ Bool
    ∷# []

Option : Fields (const Set₁)
Option = "description" ≔ Lift _ String
      ∷# "arguments"   ≔ Arguments
      ∷# []

data Modifier (nm : String) : Set₂ where
  mkFlag   : Record proj₂ Flag → Modifier nm
  mkOption : Record proj₂ Option → Modifier nm

flag : (description : String) →
       {{flag : WithDefault false}} →
       Modifier nm
flag desc {{flag}} = mkFlag $ mkRecord $ desc ∷ flag .value ∷ []

option : (description : String) →
         (arguments : Arguments) →
         Modifier nm
option desc ducer = mkOption $ mkRecord $ lift desc ∷ ducer ∷ []

ParsedModifierT : (f g : Set → Set) → Modifier nm → Set
ParsedModifierT f g (mkFlag   flg) = f Bool
ParsedModifierT f g (mkOption opt) = ParsedArgumentsT g (opt ‼ "arguments")

ParsedModifier : Modifier nm → Set
ParsedModifier (mkFlag   flg) = Bool
ParsedModifier (mkOption opt) = ParsedArguments (opt ‼ "arguments")

updateModifier :
  {mod : Modifier nm} ->
  (new : ParsedModifierT id id mod) ->
  (old : ParsedModifierT Maybe Maybe mod) ->
  Error (ParsedModifierT Maybe Maybe mod)
-- TODO: fail if flag set twice?
updateModifier      {mod = mkFlag   flg} new _          = pure (just new)
updateModifier      {mod = mkOption opt} new nothing    = pure (just new)
updateModifier {nm} {mod = mkOption opt} new (just old)
  with Arguments.domain (opt ‼ "arguments")
... | Some S = throw (optionSetTwice nm)
... | ALot M = pure (just $ let open RawMagma M in old ∙ new)

finalisingModifier : (mod : Modifier nm) →
  ParsedModifierT Maybe Maybe mod →
  Error (ParsedModifier mod)
finalisingModifier (mkFlag   flg) val =
  pure $ fromMaybe (flg ‼ "default") val
finalisingModifier {nm} (mkOption opt) val =
  Argument.finalising (missingOption nm) (opt ‼ "arguments") val

ParsedModifiersT : (f g : Set → Set) → (mods : Fields Modifier) → Set₂
ParsedModifiersT f g mods = Record (λ fld → ParsedModifierT f g (proj₂ fld)) mods

ParsedModifiers : (mods : Fields Modifier) → Set₂
ParsedModifiers mods = Record (λ fld → ParsedModifier (proj₂ fld)) mods

update :
  {p : Σ _ Modifier → Set ℓ} →
  {mods : Fields Modifier} →
  (ps : ParsedModifiersT Maybe Maybe mods) →
  (pos : Any p mods) →
  (p : ParsedModifierT id id (proj₂ $ proj₁ $ Any.witness pos)) →
  Error (ParsedModifiersT Maybe Maybe mods)
update ps pos p = Record.update pure _<*>_ ps pos
                $ const $ updateModifier {mod = proj₂ $ proj₁ $ Any.witness pos} p

finalising : {mods : Fields Modifier} →
  ParsedModifiersT Maybe Maybe mods →
  Error (ParsedModifiers mods)
finalising = Record.traverse pure _<*>_ (λ {mod} → finalisingModifier (proj₂ mod))

open import Relation.Binary using (Rel)
open import Relation.Unary using (Pred; Universal)

tabulate : ∀ {a r} {A : Set a} {P : Pred A ℓ} {R : Rel A r} → Π[ P ] → Π[ All {R = R} P ]
tabulate f []        = []
tabulate f (x ∷# xs) = f x ∷ tabulate f xs

initNothing : {mods : Fields Modifier} -> ParsedModifiersT Maybe Maybe mods
initNothing = mkRecord $ flip tabulate _ $ λ where
  (_ , mkFlag   flg) → nothing
  (_ , mkOption opt) → nothing
