module agdARGS.Data.Arguments where

open import Level
open import Data.Unit
open import Data.Bool
import Data.Product as Prod
open import Data.Maybe as Maybe
open import Data.String as Str using (String)

open import Function
open import Relation.Binary
import Relation.Binary.On as On

open import Algebra

record RawMagma (ℓ : Level) : Set (suc ℓ) where
  field
    Carrier : Set ℓ
    _∙_     : Carrier → Carrier → Carrier

data Domain (ℓ : Level) : Set (suc ℓ) where
  None :                    Domain ℓ
  Some : (S : Set ℓ)      → Domain ℓ
  ALot : (M : RawMagma ℓ) → Domain ℓ

elimDomain :
  {ℓ ℓᵖ : Level} {P : Domain ℓ → Set ℓᵖ}
  (dNone : P None) (dSome : ∀ S → P (Some S)) (dALot : ∀ M → P (ALot M)) →
  (d : Domain ℓ) → P d
elimDomain dNone dSome dALot None     = dNone
elimDomain dNone dSome dALot (Some S) = dSome S
elimDomain dNone dSome dALot (ALot M) = dALot M

record Argument (ℓ : Level) : Set (suc ℓ) where
  field
    name        : String
    description : String
    flag        : String
    optional    : Bool
    domain      : Domain ℓ
    parser      :
       let parseOne S = String → Maybe S
       in elimDomain (Lift ⊤) parseOne (parseOne ∘ RawMagma.Carrier) domain

open Argument

strictTotalOrder : (ℓ : Level) → StrictTotalOrder _ _ _
strictTotalOrder ℓ = On.strictTotalOrder Str.strictTotalOrder (flag {ℓ})

module Arguments (ℓ : Level) where

  open import agdARGS.Data.Infinities
  open import agdARGS.Data.UniqueSortedList (strictTotalOrder ℓ) public

  Arguments : Set (suc ℓ)
  Arguments = UniqueSortedList -∞ +∞

  Options : (m : Argument ℓ → Set ℓ) {lb ub : _} (args : UniqueSortedList lb ub) → Set ℓ
  Options m (lt ■)           = Lift ⊤
  Options m (hd , lt ∷ args) = m hd Prod.× Options m args

  getOptions :
    (m : Argument ℓ → Set ℓ) {lb ub : _} {args : UniqueSortedList lb ub} {arg : Argument ℓ}
    (pr : arg ∈ args) → Options m args → m arg
  getOptions m z      = Prod.proj₁
  getOptions m (s pr) = getOptions m pr ∘ Prod.proj₂

  MaybeMode : Domain ℓ → Set ℓ
  MaybeMode = elimDomain {P = const $ Set ℓ} (Lift ⊤) Maybe (Maybe ∘ RawMagma.Carrier)

  defaultOptions : {lb ub : _} (args : UniqueSortedList lb ub) → Options (MaybeMode ∘ domain) args
  defaultOptions (lt ■)           = lift tt
  defaultOptions (hd , lt ∷ args) = default Prod., defaultOptions args
    where
      default : MaybeMode $ domain hd
      default = elimDomain {P = MaybeMode} (lift tt) (λ S → nothing) (λ M → nothing) $ domain hd

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  findArgument : (str : String) (args : Arguments) →
                 Dec (Prod.Σ[ arg ∈ Argument ℓ ] (arg ∈ args Prod.× flag arg ≡ str))
  findArgument str = search Str._≟_ flag str




{-
  open import Data.List
  open import Category.Monad

  preParse : List String → (args : Arguments) → Maybe $ Options (const Maybe) args
  preParse xs args = go xs (defaultOptions args)
    where
      go : List String → Options (const Maybe) args →
           Maybe $ Options (const Maybe) args
      go []           opts = just opts
      go (x ∷ [])     opts = nothing
      go (s ∷ v ∷ xs) opts = opts′ >>= go xs
        where
          open RawMonad Maybe.monad
          opts′ : Maybe $ Options (const Maybe) args
          opts′ with getArg s args | get s opts
          opts′ | just _          | just opt = nothing
          opts′ | just (arg , _)  | nothing  = {!set ?!}
          opts′ | nothing         | q        = nothing

  validate : {args : Arguments} → Options (const Maybe) args →
             let f a = if optional a then Maybe else id
             in Maybe $ Options f args
  validate = {!!}


  parse : List String → (args : Arguments) → Maybe $ Options _ args
  parse xs args = preParse xs args >>= validate
    where open RawMonad Maybe.monad
-}