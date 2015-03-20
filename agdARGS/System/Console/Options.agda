module agdARGS.System.Console.Options where

open import Level
open import Data.Unit
open import Data.Bool
open import Data.Product as Prod
open import Data.Sum as Sum
open import Data.Maybe as Maybe
open import Data.String as Str hiding (strictTotalOrder)

open import Function
open import Relation.Binary
import Relation.Binary.On as On

open import agdARGS.System.Console.Options.Domain

record Option (ℓ : Level) : Set (suc ℓ) where
  field
    name        : String
    description : String
    flag        : String
    optional    : Bool
    domain      : Domain ℓ
    parser      : Parser domain
open Option

strictTotalOrder : (ℓ : Level) → StrictTotalOrder _ _ _
strictTotalOrder ℓ = On.strictTotalOrder Str.strictTotalOrder (flag {ℓ})

module Options (ℓ : Level) where

  open import agdARGS.Data.Infinities
  open import agdARGS.Data.UniqueSortedList (strictTotalOrder ℓ) public

  Options : Set (suc ℓ)
  Options = UniqueSortedList -∞ +∞

  Mode : {lb ub : _} (args : UniqueSortedList lb ub) → Set (suc ℓ)
  Mode args = (arg : Option ℓ) (pr : arg ∈ args) → Set ℓ

  ModeS : {lb ub : _} {hd : _} .{lt : lb < ↑ hd} {args : UniqueSortedList (↑ hd) ub} →
          Mode (hd , lt ∷ args) → Mode args
  ModeS m = λ arg → m arg ∘ s

  values : {lb ub : _} (args : UniqueSortedList lb ub) (m : Mode args) → Set ℓ
  values (lt ■)           m = Lift ⊤
  values (hd , lt ∷ args) m = m hd z × values args (ModeS m)

  -- This is a trick to facilitate type inference: when `args` is
  -- instantiated, `values` will compute, making it impossible
  -- to reconstruct `args`'s value, but `Values` will stay stuck.
  -- This is why `get` uses `Values` (and takes `args` as an
  -- implicit argument) and `parse` produces it.
  data Values (args : Options) (m : Mode args) : Set ℓ where
    mkValues : values args m → Values args m

  getValues :
    {lb ub : _} {args : UniqueSortedList lb ub} (m : Mode args)
    {arg : Option ℓ} (pr : arg ∈ args) → values args m → m arg pr
  getValues m z      = proj₁
  getValues m (s pr) = getValues (ModeS m) pr ∘ proj₂

  SetDomain : Domain ℓ → Set ℓ
  SetDomain = maybe id (Lift ⊤) ∘ Carrier

  MaybeMode : {lb ub : _} {args : UniqueSortedList lb ub} → Mode args
  MaybeMode = const ∘ Maybe ∘ SetDomain ∘ domain

  defaultValues : {lb ub : _} (args : UniqueSortedList lb ub) → values args MaybeMode
  defaultValues (lt ■)           = lift tt
  defaultValues (hd , lt ∷ args) = nothing , defaultValues args

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  findOption : (str : String) (args : Options) →
                 Dec (Σ[ arg ∈ Option ℓ ] (arg ∈ args × flag arg ≡ str))
  findOption str = search Str._≟_ flag str

  open import lib.Nullary

  genericGet :
    {args : Options} {m : Mode args} (str : String) (opts : Values args m) →
    dec (findOption str args) (uncurry $ λ arg → m arg ∘ proj₁) (const $ Lift ⊤)
  genericGet {args} {m} str (mkValues opts) = dec′ C (findOption str args) success failure
    where
      C : Dec _ → Set ℓ
      C d = dec d (uncurry $ λ arg → m arg ∘ proj₁) (const $ Lift ⊤)

      success : ∀ p → C (yes p)
      success (arg , pr , _) = getValues m pr opts

      failure : ∀ ¬p → C (no ¬p)
      failure = const $ lift tt

  open import Category.Monad

  mapMValues :
     {M : Set ℓ → Set ℓ} (MM : RawMonad M) →
     {lb ub : _} (args : UniqueSortedList lb ub) {f g : Mode args}
     (upd : (arg : Option ℓ) (pr : arg ∈ args) → f arg pr → M (g arg pr)) →
     values args f → M (values args g)
  mapMValues MM (lt ■)         upd opts       = let open RawMonad MM in return opts
  mapMValues MM (hd , lt ∷ xs) upd (v , opts) =
    upd hd z v                                   >>= λ w  →
    mapMValues MM xs (λ arg → upd arg ∘ s) opts >>= λ ws →
    return (w , ws)
    where open RawMonad MM

  updateMValues :
     {M : Set ℓ → Set ℓ} (MM : RawMonad M) →
     {lb ub : _} {args : UniqueSortedList lb ub} {m : Mode args}
     {arg : Option ℓ} (pr : arg ∈ args) (f : m arg pr → M (m arg pr)) →
     values args m → M (values args m)
  updateMValues {M} MM {args = args} {m} {arg} pr f = mapMValues MM _ (upd m pr f)
    where
      open RawMonad MM

      upd : {lb ub : _} {args : UniqueSortedList lb ub} (m : Mode args) {arg : Option ℓ} →
            (pr : arg ∈ args) (upd : m arg pr → M (m arg pr)) → 
            (arg : Option ℓ) (pr : arg ∈ args) → m arg pr → M (m arg pr)
      upd m z       f arg z       = f
      upd m z       f arg (s pr₂) = return
      upd m (s pr₁) f arg z       = return
      upd m (s pr₁) f arg (s pr₂) = upd (ModeS m) pr₁ f arg pr₂

  import agdARGS.Data.Sum as Sum
  open import agdARGS.Algebra.Magma

  set : {args : Options} {arg : Option ℓ} (pr : arg ∈ args) (v : SetDomain (domain arg)) →
        values args MaybeMode → String ⊎ values args MaybeMode
  set {_} {arg} pr v = updateMValues (Sum.monad String) pr $ elimDomain {P = P} PNone PSome PALot (domain arg) v
    where
      P : Domain ℓ → Set ℓ
      P d = SetDomain d → Maybe (SetDomain d) → String ⊎ Maybe (SetDomain d)

      PNone : P None
      PNone new = maybe′ (const (inj₁ ("Flag " ++ flag arg ++ " set more than once"))) (inj₂ (just new))

      PSome : (S : Set ℓ) → P (Some S)
      PSome S new = maybe′ (const (inj₁ ("Option " ++ flag arg ++ " used more than once"))) (inj₂ (just new))

      PALot : (M : RawMagma ℓ) → P (ALot M)
      PALot M new = maybe′ (λ old → inj₂ (just (new ∙ old))) (inj₂ (just new))
        where open RawMagma M

  open import Data.Nat as Nat
  open import Data.List using ([] ; _∷_ ; List)
  open import lib.Nullary

  ParseResult : (args : Options) → Maybe (Option ℓ) → Set ℓ
  ParseResult args default = maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) default × values args MaybeMode

  parse : List String → (default : Maybe (Option ℓ)) (args : Options) →
          String ⊎ maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) default × Values args MaybeMode
  parse xs default args = Sum.map id (Prod.map id mkValues) $ go xs (initDefault , defaultValues args)
    where

      initDefault : maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) default
      initDefault = maybe {B = maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤)} (λ _ → nothing) (lift tt) default

      failure : String → ParseResult args default → String ⊎ ParseResult args default
      failure x (opt , opts) =
        (case default
         return (λ d → maybe (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) d → String ⊎ ParseResult args d)
         of λ { nothing    _ → inj₁ ("Invalid option: " ++ x)
              ; (just arg) →
                (case (domain arg)
                return (λ d → Parser d → Maybe (SetDomain d) →
                              String ⊎ (Maybe (SetDomain d) × values args MaybeMode))
                of λ { None     p old → inj₁ "Defaulting should always work on a RawMagma"
                     ; (Some S) p old → inj₁ "Defaulting should always work on a RawMagma"
                     ; (ALot M) p old →
                         let open RawMonad (Sum.monad String {ℓ})
                             open RawMagma M
                         in (λ v → (maybe (λ w → just (v ∙ w)) (just v) old , opts)) <$> p x
                     }) (parser arg)
              }) opt

      go : List String → ParseResult args default → String ⊎ ParseResult args default
      go []           opts         = inj₂ opts
      go (x ∷ [])     (opt , opts) =
        flip (dec (findOption x args))
        -- flag not found
        (const $ failure x (opt , opts))
        -- flag found
        $ λ elpreq →
        let sd = case domain (proj₁ elpreq)
                 return (λ d → String ⊎ SetDomain d)
                 of λ { None → inj₂ (lift tt)
                      ; _    → inj₁ ("Option " ++ flag (proj₁ elpreq) ++ " expects an argument; none given") }
            open RawMonad (Sum.monad String {ℓ})
        in sd >>= λ v → set (proj₁ (proj₂ elpreq)) v opts >>= λ opts′ → return (opt , opts′)
      go (x ∷ y ∷ xs) (opt , opts) =
        flip (dec (findOption x args))
        -- flag not found
        (const $
          let open RawMonad (Sum.monad String {ℓ})
          in failure x (opt , opts) >>= go (y ∷ xs))
        -- flag found
        $ λ elpreq →
        let vb = (case domain (proj₁ elpreq)
                  return (λ d → Parser d → String ⊎ (SetDomain d × Bool))
                  of let open RawMonad (Sum.monad String {ℓ}) in λ
                     { None     p → inj₂ (lift tt , false)
                     ; (Some S) p → (λ s → s , true) <$> p y
                     ; (ALot M) p → (λ s → s , true) <$> p y }
                 ) (parser (proj₁ elpreq))
            open RawMonad (Sum.monad String {ℓ})
        in vb >>= uncurry λ v b → set (proj₁ (proj₂ elpreq)) v opts >>= λ opts′ →
           (if b then go xs else go (y ∷ xs)) (opt , opts′)

{-
  validate : {args : Values} → Values (const Maybe) args →
             let f a = if optional a then Maybe else id
             in Maybe $ Values f args
  validate = {!!}


  parse : List String → (args : Values) → Maybe $ Values _ args
  parse xs args = preParse xs args >>= validate
    where open RawMonad Maybe.monad
-}
  open import agdARGS.Data.UniqueSortedList.SmartConstructors (strictTotalOrder ℓ) public