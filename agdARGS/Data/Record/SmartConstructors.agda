open import Level
open import Relation.Binary

module agdARGS.Data.Record.SmartConstructors
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Product as Prod
open import Data.Maybe
open import Function
open import Category.Monad
open import agdARGS.Relation.Nullary
open import agdARGS.Data.Infinities
open import agdARGS.Data.UniqueSortedList STO as USL hiding (module withEqDec)
open import agdARGS.Data.UniqueSortedList.SmartConstructors STO
open import agdARGS.Data.Record STO as Rec


⟨⟩ : ∀ {ℓ} → Record {ℓ} `[] _
⟨⟩ = _

infixr 5 _∷=_⟨_ 
_∷=_⟨_ : ∀ {ℓ} {args : USL} {f : Fields ℓ args} arg {S : Set ℓ} → S →
         Record args f → Record _ _
arg ∷= v ⟨ r = let open Rec.NeverFail in Rinsert arg (-∞<↑ arg) ↑ arg <+∞ v r

{-
[⟨⟩] : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args} → [MRecord] args f
[⟨⟩] {args = _ ■}            = lift tt
[⟨⟩] {args = hd , lt ∷ args} = nothing , [⟨⟩]

⟨⟩ : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} → MRecord args f
⟨⟩ = mkMRecord [⟨⟩]

infixr 5 [_at_∷=_⟨]_ _at_∷=_⟨_
[_at_∷=_⟨]_ : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
              arg (pr : arg ∈ args) (v : [lookup] pr f) →
              [MRecord] args f → [MRecord] args f
[ a at z    ∷= v ⟨] (_ , r) = just v , r
[ a at s pr ∷= v ⟨] (w , r) = w      , [ a at pr ∷= v ⟨] r

_at_∷=_⟨_ : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
            arg (pr : arg ∈ args) (v : lookup pr f) →
            MRecord args f → MRecord args f
a at pr ∷= v ⟨ r = mkMRecord $ [ a at pr ∷= v ⟨] mcontent r


[weaken] : ∀ {ℓ hd lb ub} {args : UniqueSortedList lb ub} .(lt : hd < lb) →
           [Fields] ℓ args → [Fields] ℓ (weaken lt args)
[weaken] {args = lt ■}           lt′ f       = f
[weaken] {args = hd , lt ∷ args} lt′ (S , f) = S , f

[Weaken] :
  ∀ {ℓ hd lb ub} {args : UniqueSortedList lb ub} .(lt : hd < lb) {f : [Fields] ℓ args} →
  [Record] args f → [Record] (weaken lt args) ([weaken] lt f)
[Weaken] {args = lt ■}           lt′ mr = lift tt
[Weaken] {args = hd , lt ∷ args} lt′ mr = mr

[freeze] : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args} →
          [MRecord] args f → Maybe ([Record] args f)
[freeze] {args = lt ■}           mr                      = just _
[freeze] {args = hd , lt ∷ args} {f = (S , f)} (mv , mr) = _,_ <$> mv ⊛ [freeze] mr
  where open RawMonad monad

mfreeze : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
         (mr : MRecord args f) → Maybe (Record args f)
mfreeze mr = let open RawMonad monad in mkRecord <$> [freeze] (mcontent mr)

freeze : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
         (mr : MRecord args f) → From-just (Record args f) (mfreeze mr)
freeze mr = from-just (mfreeze mr)

{-
[allJust] : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args} →
            [MRecord] args f → Maybe ([Record] args f)
[allJust] {args = lt ■}           r        = just r
[allJust] {args = hd , lt ∷ args} (mv , r) = _,_ <$> mv ⊛ [allJust] r
  where open RawMonad monad

allJust :  ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} →
           MRecord args f → Maybe (Record args f)
allJust (mkMRecord r) = mkRecord <$> [allJust] r
  where open RawMonad monad

freeze : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} →
         (r : MRecord args f) {pr : T (is-just (allJust r))} → Record args f
freeze r {pr} = to-witness-T (allJust r) pr
-}

{-
Dummy : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args
Dummy ℓ = tabulate $ const $ Lift ⊤

⟨⟩ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Record args (Dummy ℓ)
⟨⟩ = pure go where
  go : {lb ub : _} {args : UniqueSortedList lb ub} (arg : _) (pr : arg ∈ args) →
       [lookup] pr (fields $ Dummy _)
  go arg z      = lift tt
  go arg (s pr) = go arg pr 

[update] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → [Fields] ℓ args →
           {arg : _} (pr : arg ∈ args) (A : Set ℓ) → [Fields] ℓ args
[update] (_ , fs) z      A = A , fs
[update] (f , fs) (s pr) A = f , [update] fs pr A

update : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} → Fields ℓ args →
        {arg : _} (pr : arg ∈ args) (A : Set ℓ) → Fields ℓ args
update f pr A = mkFields $ [update] (fields f) pr A

infixr 5 [_at_∷=_⟨]_ _at_∷=_⟨_
[_at_∷=_⟨]_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args}
              (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
              [Record] args f → [Record] args ([update] f pr A)
[ a at z    ∷= v ⟨] (_ , r) = v , r
[ a at s pr ∷= v ⟨] (w , r) = w , [ a at pr ∷= v ⟨] r

_at_∷=_⟨_ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
            (arg : _) (pr : arg ∈ args) {A : Set ℓ} (v : A) →
            Record args f → Record args (update f pr A)
a at pr ∷= v ⟨ r = mkRecord $ [ a at pr ∷= v ⟨] content r
-}
-}
open import Relation.Binary.PropositionalEquality

module withEqDec
       (eqDec : Decidable ((StrictTotalOrder.Carrier STO → _ → Set ℓᵃ) ∋ _≡_))
       where

  open USL.withEqDec eqDec
  open import Relation.Nullary

{-
  infixr 5 _∷=_⟨_
  _∷=_⟨_ : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args}
           arg {pr : toSet (arg ∈? args)} (v : lookup (fromYes (arg ∈? args) {pr}) f) →
           MRecord args f → MRecord args f
  _∷=_⟨_ {args = args} arg {pr} v r with arg ∈? args
  ... | yes p = arg at p ∷= v ⟨ r
  ... | no ¬p = ⊥-elim pr
-}

  `project : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} arg →
             Record args f → dec (arg ∈? args) (λ pr → lookup pr f) (const $ Lift ⊤)
  `project {args = args} arg r with arg ∈? args
  ... | yes pr = project pr r
  ... | no ¬pr = lift tt

  _‼_ : ∀ {ℓ} {lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} →
        Record args f → ∀ arg → {pr : toSet (arg ∈? args)} →
        lookup (fromYes (arg ∈? args) {pr}) f
  _‼_ {args = args} r arg {pr} with arg ∈? args
  ... | yes p = project p r
  ... | no ¬p = ⊥-elim pr
