module agdARGS.Data.Arguments where

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

open import agdARGS.Algebra.Magma

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

Parser : {ℓ : Level} → Domain ℓ → Set ℓ
Parser =
  let parseOne S = String → String ⊎ S
  in elimDomain (Lift ⊤) parseOne (parseOne ∘ RawMagma.Carrier)

record Argument (ℓ : Level) : Set (suc ℓ) where
  field
    name        : String
    description : String
    flag        : String
    optional    : Bool
    domain      : Domain ℓ
    parser      : Parser domain

open Argument

strictTotalOrder : (ℓ : Level) → StrictTotalOrder _ _ _
strictTotalOrder ℓ = On.strictTotalOrder Str.strictTotalOrder (flag {ℓ})

module Arguments (ℓ : Level) where

  open import agdARGS.Data.Infinities
  open import agdARGS.Data.UniqueSortedList (strictTotalOrder ℓ) public
  open import agdARGS.Data.UniqueSortedList.SmartConstructors (strictTotalOrder ℓ) public

  Arguments : Set (suc ℓ)
  Arguments = UniqueSortedList -∞ +∞

  mode : (ℓᵐ : Level) {lb ub : _} (args : UniqueSortedList lb ub) → Set (suc ℓᵐ)
  mode ℓᵐ (lt ■)         = Lift ⊤
  mode ℓᵐ (hd , lt ∷ xs) = Set ℓᵐ × mode ℓᵐ xs

  data _<_∈_<_by_
    {ℓᵐ : Level} (arg : Argument ℓ) (S : Set ℓᵐ) :
    {lb ub : _} (args : UniqueSortedList lb ub) (m : mode ℓᵐ args) (pr : arg ∈ args) → Set (suc (ℓ ⊔ ℓᵐ)) where
    z : ∀ {lb ub} {xs : UniqueSortedList (↑ arg) ub} {m} .{lt : lb < ↑ arg} → arg < S ∈ arg , lt ∷ xs < S , m by z
    s : ∀ {lb ub hd} {xs : UniqueSortedList (↑ hd) ub} {T m pr} .{lt : lb < ↑ hd}
          (n : arg < S ∈ xs < m by pr) →
          arg < S ∈ hd , lt ∷ xs < T , m by s pr

  record Mode (ℓᵐ : Level) (args : Arguments) : Set (suc ℓᵐ) where
    constructor mkMode
    field
      outMode : mode ℓᵐ args
  open Mode

  tabulateMode :
    {ℓᵐ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
    (f : (arg : Argument ℓ) (pr : arg ∈ args) → Set ℓᵐ) →
    mode ℓᵐ args
  tabulateMode (lt ■)         f = lift tt
  tabulateMode (hd , lt ∷ xs) f = f hd z , tabulateMode xs (λ arg → f arg ∘ s)
  
  infix 5 _‼_
  _‼_ : {ℓᵐ : Level} {lb ub : _} {args : UniqueSortedList lb ub} (m : mode ℓᵐ args)
        {arg : Argument ℓ} (pr : arg ∈ args) → Set ℓᵐ
  (m , _)  ‼ z    = m
  (_ , ms) ‼ s pr = ms ‼ pr

  singleton : 
    {ℓᵐ : Level} {arg : Argument ℓ} {lb ub : _} {args : UniqueSortedList lb ub}
    (m : mode ℓᵐ args) (pr : arg ∈ args) → arg < m ‼ pr ∈ args < m by pr
  singleton m z      = z
  singleton m (s pr) = s (singleton (proj₂ m) pr)

  infixl 6 _⟨_∷=_
  _⟨_∷=_ : {ℓᵐ : Level} {lb ub : _} {args : UniqueSortedList lb ub} (m : mode ℓᵐ args)
           {arg : Argument ℓ} (pr : arg ∈ args) (S : Set ℓᵐ) → mode ℓᵐ args
  (_ , ms) ⟨ z    ∷= S = S , ms
  (m , ms) ⟨ s pr ∷= S = m , ms ⟨ pr ∷= S

{-
  _⊨_→M_ : (M : Set ℓ → Set ℓ) {lb ub : _} {args : UniqueSortedList lb ub} (m n : mode ℓᵐ args) → Set (suc ℓᵐ)
  M ⊨ m →M n = {arg : Argument ℓ} (pr : arg ∈ _) → m ‼ pr → M $ n ‼ pr
-}

  options : {ℓᵐ : Level} {lb ub : _} (args : UniqueSortedList lb ub) (m : mode ℓᵐ args) → Set ℓᵐ
  options (lt ■)           _        = Lift ⊤
  options (hd , lt ∷ args) (m , ms) = m × options args ms

  -- This is a trick to facilitate type inference: when `args` is
  -- instantiated, `options` will compute, making it impossible
  -- to reconstruct `args`'s value, but `Options` will stay stuck.
  -- This is why `get` uses `Options` (and takes `args` as an
  -- implicit argument) and `parse` produces it.
  record Options {ℓᵐ : Level} (args : Arguments) (m : Mode ℓᵐ args) : Set ℓᵐ where
    constructor mkOptions
    field
      outOptions : options args (outMode m)
  open Options

  getOptions :
    {ℓᵐ : Level} {lb ub : _} {args : UniqueSortedList lb ub} (m : mode ℓᵐ args)
    {arg : Argument ℓ} (pr : arg ∈ args) → options args m → m ‼ pr
  getOptions m        z      = proj₁
  getOptions (_ , ms) (s pr) = getOptions ms pr ∘ proj₂

  open import Category.Monad

  infixl 6 _⟪_←[_]_ _⟪_←_
  _⟪_←[_]_ :
    {ℓᵐ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
    {m : mode ℓᵐ args} (opts : options args m) {arg : Argument ℓ} {pr : arg ∈ args}
    {S T : Set ℓᵐ} → arg < S ∈ args < m by pr → 
    {M : Set ℓᵐ → Set ℓᵐ} (MM : RawMonad M) (f : S → M T) → M $ options args (m ⟨ pr ∷= T)
  (opt , opts) ⟪ z    ←[ MM ] f = let open RawMonad MM in flip _,_ opts <$> f opt
  (opt , opts) ⟪ s pr ←[ MM ] f = let open RawMonad MM in _,_ opt       <$> opts ⟪ pr ←[ MM ] f

  _⟪_←_ :
    {ℓᵐ : Level} {args : Arguments} {m : Mode ℓᵐ args}
    (opts : Maybe $ Options args m)
    {arg : Argument ℓ} {pr : arg ∈ args} {S : Set ℓᵐ} → arg < Maybe S ∈ args < outMode m by pr →
    {T : Set ℓᵐ} (f : Maybe S → Maybe T) → Maybe $ Options args (mkMode (outMode m ⟨ pr ∷= T))
  opts ⟪ pr ← f = mkOptions <$> (opts >>= λ opts → (outOptions opts ⟪ pr ←[ Maybe.monad ] f))
    where open RawMonad Maybe.monad

  SetDomain : Domain ℓ → Set ℓ
  SetDomain = elimDomain {P = const $ Set ℓ} (Lift ⊤) id (RawMagma.Carrier)

  IdentityMode : {lb ub : _} {args : UniqueSortedList lb ub} → mode ℓ args
  IdentityMode = tabulateMode _ $ const ∘ SetDomain ∘ domain

  MaybeMode : {args : Arguments} → Mode ℓ args
  MaybeMode = mkMode $ tabulateMode _ $ const ∘ Maybe ∘ SetDomain ∘ domain

{-
  [_]_⟪_←_ :
    {ℓᵐ : Level} {args : Arguments}
    {M : Set ℓᵐ → Set ℓᵐ} (MM : RawMonad M)
    {m : Mode ℓᵐ args} (opts : M (Options args m)) {arg : Argument ℓ}
    (pr : arg ∈ args) {S : Set ℓᵐ} (f : outMode m ‼ pr → M S) → M $ Options args (mkMode (outMode m ⟨ pr ∷= S))
  [ MM ] mopts ⟪ pr ← f =
    let open RawMonad MM in
    mopts >>= λ opts → mkOptions <$> outOptions opts ⟪ pr ←[ MM ] f

  -- this is not going to work. Maybe we simply need something
  -- simpler: a way to combine various validation processes. At
  -- the variable level, we may describe them using _⟪_←[_]_ but
  -- we should be able to compose them!
  --_isMandatory : 
  --  {ℓᵐ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
  --  {m : mode ℓᵐ args} {arg : Argument ℓ} (pr : arg ∈ args) →
  --  options args MaybeMode → Maybe $ options args (MaybeMode ⟨ pr ∷= SetDomain (domain arg))
  --(pr isMandatory) opts = opts ⟪ pr ←[ monad ] {!!}
-}
{-
  (_ , opts) ⟪ z    ∷= opt = opt , opts
  (v , opts) ⟪ s pr ∷= opt = v , opts ⟪ pr ∷= opt

  SetDomain : Domain ℓ → Set ℓ
  SetDomain = elimDomain {P = const $ Set ℓ} (Lift ⊤) id (RawMagma.Carrier)

  IdentityMode : {lb ub : _} {args : UniqueSortedList lb ub} → Mode args
  IdentityMode = const ∘ SetDomain ∘ domain

  MaybeMode : {lb ub : _} {args : UniqueSortedList lb ub} → Mode args
  MaybeMode = const ∘ Maybe ∘ SetDomain ∘ domain

  defaultOptions : {lb ub : _} (args : UniqueSortedList lb ub) → options args MaybeMode
  defaultOptions (lt ■)           = lift tt
  defaultOptions (hd , lt ∷ args) = nothing , defaultOptions args

  open import Relation.Nullary
  open import Relation.Binary.PropositionalEquality

  findArgument : (str : String) (args : Arguments) →
                 Dec (Σ[ arg ∈ Argument ℓ ] (arg ∈ args × flag arg ≡ str))
  findArgument str = search Str._≟_ flag str

  open import lib.Nullary

  genericGet :
    {args : Arguments} {m : Mode args} (str : String) (opts : Options args m) →
    dec (findArgument str args) (uncurry $ λ arg → m arg ∘ proj₁) (const $ Lift ⊤)
  genericGet {args} {m} str (mkOptions opts) = dec′ C (findArgument str args) success failure
    where
      C : Dec _ → Set ℓ
      C d = dec d (uncurry $ λ arg → m arg ∘ proj₁) (const $ Lift ⊤)

      success : ∀ p → C (yes p)
      success (arg , pr , _) = getOptions m pr opts

      failure : ∀ ¬p → C (no ¬p)
      failure = const $ lift tt

  get : {args : Arguments} (str : String) (opts : Options args MaybeMode) → _
  get = genericGet

  open import Category.Monad

  mapMOptions :
     {M : Set ℓ → Set ℓ} (MM : RawMonad M) →
     {lb ub : _} (args : UniqueSortedList lb ub)
     {f g : Mode args} (φ : M ⊨ f →M g) → options args f → M (options args g)
  mapMOptions MM (lt ■)         φ opts       = let open RawMonad MM in return opts
  mapMOptions MM (hd , lt ∷ xs) φ (v , opts) =
    φ hd z v                                   >>= λ w  →
    mapMOptions MM xs (λ arg → φ arg ∘ s) opts >>= λ ws →
    return (w , ws)
    where open RawMonad MM

  _⊨if≡_then_else_ :
    (M : Set ℓ → Set ℓ) {lb ub : _} {args : UniqueSortedList lb ub} {m n : Mode args}
    {arg : Argument ℓ} (pr : arg ∈ args) (f : m arg pr → M (n arg pr)) →
    (g : M ⊨ m →M n) → M ⊨ m →M n
  (M ⊨if≡ z     then f else g) arg z       v = f v
  (M ⊨if≡ s pr₁ then f else g) arg (s pr₂) v = (M ⊨if≡ pr₁ then f else (λ arg → g arg ∘ s)) arg pr₂ v
  (M ⊨if≡ z     then f else g) arg (s pr₂) v = g arg (s pr₂) v
  (M ⊨if≡ s pr₁ then f else g) arg z       v = g arg z v

  if≡_then_else_ :
    {lb ub : _} {args : UniqueSortedList lb ub} {ℓᵖ : Level}
    {P : (arg : Argument ℓ) (pr : arg ∈ args) → Set ℓᵖ}
    {arg : Argument ℓ} (pr : arg ∈ args) (p : P arg pr) →
    (m : (arg : Argument ℓ) (pr : arg ∈ args) → P arg pr) → 
    (arg : Argument ℓ) (pr : arg ∈ args) → P arg pr
  (if≡ z     then p else m) arg z       = p
  (if≡ s pr₁ then p else m) arg (s pr₂) = (if≡ pr₁ then p else (λ arg → m arg ∘ s)) arg pr₂
  (if≡ z     then p else m) arg (s pr₂) = m arg (s pr₂)
  (if≡ s pr₁ then p else m) arg z       = m arg z

  branch :
    {lb ub : _} {args : UniqueSortedList lb ub} {ℓPQ : Level}
    (P : (arg : Argument ℓ) (pr : arg ∈ args) → Set ℓPQ)
    (Q : (arg : Argument ℓ) (pr : arg ∈ args) → Set ℓPQ)
    {arg : Argument ℓ} (pr₁ : arg ∈ args) (p : P arg pr₁) →
    (m : (arg : Argument ℓ) (pr : arg ∈ args) → Q arg pr) → 
    (arg : Argument ℓ) (pr₂ : arg ∈ args) → (if≡ pr₁ then P _ pr₁ else Q) arg pr₂
  branch P Q z       p m arg z       = p
  branch P Q z       p m arg (s pr₂) = m arg (s pr₂)
  branch P Q (s pr₁) p m arg z       = m arg z
  branch P Q (s pr₁) p m arg (s pr₂) = branch P′ Q′ pr₁ p (λ arg → m arg ∘ s) arg pr₂
    where P′ = λ arg → P arg ∘ s
          Q′ = λ arg → Q arg ∘ s

  _isMandatory :
    {lb ub : _} {args : UniqueSortedList lb ub} {arg : Argument ℓ}
    (pr : arg ∈ args) → options args MaybeMode →
    Maybe $ options args (if≡ pr then (IdentityMode arg pr) else MaybeMode)
  pr₁ isMandatory = mapMOptions monad _ (λ arg pr₂ v → 
       let w val = branch IdentityMode MaybeMode pr₁ val {!!} {!!} pr₂
       in maybe {!just ∘ w!} {!!} v)

  updateMOptions :
     {M : Set ℓ → Set ℓ} (MM : RawMonad M) →
     {lb ub : _} {args : UniqueSortedList lb ub} {m : Mode args}
     {arg : Argument ℓ} (pr : arg ∈ args) (f : m arg pr → M (m arg pr)) →
     options args m → M (options args m)
  updateMOptions {M} MM pr f = mapMOptions MM _ (M ⊨if≡ pr then f else (λ _ _ → RawMonad.return MM))

  import agdARGS.Data.Sum as Sum

  set : {args : Arguments} {arg : Argument ℓ} (pr : arg ∈ args) (v : SetDomain (domain arg)) →
        options args MaybeMode → String ⊎ options args MaybeMode
  set {_} {arg} pr v = updateMOptions (Sum.monad String) pr $ elimDomain {P = P} PNone PSome PALot (domain arg) v
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

  ParseResult : (args : Arguments) → Maybe (Argument ℓ) → Set ℓ
  ParseResult args default = maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) default × options args MaybeMode

  parse : List String → (default : Maybe (Argument ℓ)) (args : Arguments) →
          String ⊎ maybe′ (Maybe ∘ SetDomain ∘ domain) (Lift ⊤) default × Options args MaybeMode
  parse xs default args = Sum.map id (Prod.map id mkOptions) $ go xs (initDefault , defaultOptions args)
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
                              String ⊎ (Maybe (SetDomain d) × options args MaybeMode))
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
        flip (dec (findArgument x args))
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
        flip (dec (findArgument x args))
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
  validate : {args : Arguments} → Options (const Maybe) args →
             let f a = if optional a then Maybe else id
             in Maybe $ Options f args
  validate = {!!}


  parse : List String → (args : Arguments) → Maybe $ Options _ args
  parse xs args = preParse xs args >>= validate
    where open RawMonad Maybe.monad
-}
  open import agdARGS.Data.UniqueSortedList.SmartConstructors (strictTotalOrder ℓ) public
-}