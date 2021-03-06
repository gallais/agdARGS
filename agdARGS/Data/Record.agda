open import Level
open import Relation.Binary

module agdARGS.Data.Record
       {ℓᵃ ℓᵉ ℓʳ : Level}
       (STO : StrictTotalOrder ℓᵃ ℓᵉ ℓʳ)
       where

open import Data.Unit
open import Data.Maybe hiding (map)
open import Data.Product hiding (map)
open import Function
open import Category.Applicative

-- A Record is characterised by a set of field names. We decide
-- to represent this set by a UniqueSortedList in order to ensure
-- unicity of field names. Hence the following import:

open import agdARGS.Data.Infinities hiding ([_])
open import agdARGS.Data.UniqueSortedList STO
open import agdARGS.Data.UniqueSortedList.SmartConstructors STO as SC
  hiding (module MayFail ; module NeverFail)


-- We then need to define what the content of each one of these
-- fields is. This is taken care of by associating a set to each
-- index of the UniqueSortedList of field names.

[Fields] : (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) → Set (suc ℓ)
[Fields] ℓ (_ ■)          = Lift ⊤
[Fields] ℓ (_ , _ ∷ args) = Set ℓ × [Fields] ℓ args

record Fields (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) : Set (suc ℓ) where
  constructor mkFields
  field
    fields : [Fields] ℓ args
open Fields public

-- We expect to be able to lookup a field's type from a Fields definition
[lookup] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
           {arg : _} (pr : arg ∈ args) (fs : [Fields] ℓ args) → Set ℓ
[lookup] z      (f , _)  = f
[lookup] (s pr) (_ , fs) = [lookup] pr fs

lookup : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
         {arg : _} (pr : arg ∈ args) (fs : Fields ℓ args) → Set ℓ
lookup pr = [lookup] pr ∘ fields

-- We may tabulate a function associating, to each element, a Set in order
-- to get a Fields. Cue the simplest examples: constant Set ℓ.

[tabulate] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
             (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ) → [Fields] ℓ args
[tabulate] (_ ■)            ρ = lift tt
[tabulate] (arg , _ ∷ args) ρ = ρ z , [tabulate] args (ρ ∘ s)

tabulate : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
           (ρ : {arg : _} (pr : arg ∈ args) → Set ℓ) → Fields ℓ args
tabulate {args = args} = mkFields ∘ [tabulate] args

[Sets] : (ℓ : Level) {lb ub : _} (args : UniqueSortedList lb ub) → [Fields] (suc ℓ) args
[Sets] ℓ args = [tabulate] args $ const $ Set ℓ

Sets : (ℓ : Level) {lb ub : _} {args : UniqueSortedList lb ub} → Fields (suc ℓ) args
Sets ℓ = tabulate $ const $ Set ℓ

-- We can apply a set transformer to each one the elements. This will
-- be useful later on when dealing with records whose elements are
-- in an applicative functor or a monad

[_[_]] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} →
         (a : Set ℓ → Set ℓ) → [Fields] ℓ args → [Fields] ℓ args
[_[_]] {args = _ ■}          a f        = f
[_[_]] {args = _ , _ ∷ args} a (f , fs) = a f , [ a [ fs ]]

infix 5 _[_]
_[_] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} →
       (a : Set ℓ → Set ℓ) → Fields ℓ args → Fields ℓ args
a [ f ] = mkFields [ a [ fields f ]]

-- A record is then defined by aggregating an element of each one
-- of these sets in a right-nested tuple.

[Record] : ∀ {ℓ lb ub} (args : UniqueSortedList lb ub) (f : [Fields] ℓ args) → Set ℓ
[Record] (lt ■)           f        = Lift ⊤
[Record] (hd , lt ∷ args) (f , fs) = f × [Record] args fs

record Record {ℓ lb ub} (args : UniqueSortedList lb ub) (f : Fields ℓ args) : Set ℓ where
  constructor mkRecord
  field
    content : [Record] args (fields f)
open Record public


module NeverFail where

  open SC.NeverFail

  -- We may also insert a new field
  [Finsert] : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub}
              arg .lt₁ .lt₂ → Set ℓ → [Fields] ℓ args → [Fields] ℓ (insert′ arg lt₁ lt₂ args)
  [Finsert] {args = lt ■}           a lt₁ lt₂ S f = S , _
  [Finsert] {args = hd , lt ∷ args} a lt₁ lt₂ S f with compare (↑ a) (↑ hd)
  ... | tri< lt′ ¬eq ¬gt = S , f
  ... | tri≈ ¬lt eq  ¬gt = S , proj₂ f
  ... | tri> ¬lt ¬eq gt  = proj₁ f , [Finsert] a gt lt₂ S (proj₂ f)

  Finsert : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub}
            arg .lt₁ .lt₂ → Set ℓ → Fields ℓ args → Fields ℓ (insert′ arg lt₁ lt₂ args)
  Finsert arg lt₁ lt₂ S (mkFields f) = mkFields ([Finsert] arg lt₁ lt₂ S f)

  [Rinsert] : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : [Fields] ℓ args} arg .lt₁ .lt₂ →
              {S : Set ℓ} (v : S) → [Record] args f → [Record] _ ([Finsert] arg lt₁ lt₂ S f)
  [Rinsert] {args = lt ■}           a lt₁ lt₂ S f = S , _
  [Rinsert] {args = hd , lt ∷ args} a lt₁ lt₂ S f with compare (↑ a) (↑ hd)
  ... | tri< lt′ ¬eq ¬gt = S , f
  ... | tri≈ ¬lt eq  ¬gt = S , proj₂ f
  ... | tri> ¬lt ¬eq gt  = proj₁ f , [Rinsert] a gt lt₂ S (proj₂ f)

  Rinsert : ∀ {ℓ lb ub} {args : UniqueSortedList lb ub} {f : Fields ℓ args} arg .lt₁ .lt₂ →
            {S : Set ℓ} (v : S) → Record args f → Record _ (Finsert arg lt₁ lt₂ S f)
  Rinsert arg lt₁ lt₂ v (mkRecord r) = mkRecord ([Rinsert] arg lt₁ lt₂ v r)


[foldr] : ∀ {ℓ ℓ′ lb ub} {names : UniqueSortedList lb ub} {A : Set ℓ′} {f : ∀ {n} (pr : n ∈ names) → Set ℓ} →
          (∀ {n} pr → f {n} pr → A → A) → A → [Record] names ([tabulate] names f) → A
[foldr] {names = lt ■}            c n r       = n
[foldr] {names = hd , lt ∷ names} c n (v , r) = c z v $ [foldr] (c ∘ s) n r

foldr : ∀ {ℓ ℓ′ lb ub} {names : UniqueSortedList lb ub}  {A : Set ℓ′} {f : ∀ {n} (pr : n ∈ names) → Set ℓ} →
        (∀ {n} pr → f {n} pr → A → A) → A → Record names (tabulate f) → A
foldr c n = [foldr] c n ∘ content

[MRecord] : ∀ {ℓ lb ub} (args : UniqueSortedList lb ub) (f : [Fields] ℓ args) → Set ℓ
[MRecord] (lt ■)           f        = Lift ⊤
[MRecord] (hd , lt ∷ args) (f , fs) = Maybe f × [MRecord] args fs

record MRecord {ℓ lb ub} (args : UniqueSortedList lb ub) (f : Fields ℓ args) : Set ℓ where
  constructor mkMRecord
  field
    mcontent : [MRecord] args (fields f)
open MRecord public

-- The first thing we expect Records to deliver is the ability to
-- project the content of a field given its name.

[project] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
            {arg : _} (pr : arg ∈ args) → [Record] args fs → [lookup] pr fs
[project] z      (v , _) = v
[project] (s pr) (_ , r) = [project] pr r

project : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args}
          {arg : _} (pr : arg ∈ args) → Record args fs → lookup pr fs
project pr = [project] pr ∘ content

[project′] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
             {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
             {arg : _} (pr : arg ∈ args) → [Record] args ([tabulate] args fs) → fs pr
[project′] z      (v , _) = v
[project′] (s pr) (_ , r) = [project′] pr r

project′ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
           {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
           {arg : _} (pr : arg ∈ args) → Record args (tabulate fs) → fs pr
project′ pr = [project′] pr ∘ content

-- A record of Sets can naturally be turned into the appropriate Fields
-- This is how we end up typing records with records

[Type] : {ℓ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
         (r : [Record] args ([Sets] ℓ args)) → [Fields] ℓ args
[Type] (_ ■)           _       = lift tt
[Type] (_ , _ ∷ args) (v , r) = v , [Type] args r

Type : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (r : Record args (Sets ℓ)) → Fields ℓ args
Type = mkFields ∘ [Type] _ ∘ content

-- If we know how to populate fields, we naturally want to be able
-- to build a record by tabulating the defining function.

[pure] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
         (v : (arg : _) (pr : arg ∈ args) → [lookup] pr fs) → [Record] args fs
[pure] {args = lt ■}           v = lift tt
[pure] {args = hd , lt ∷ args} v = v _ z , [pure] (λ a → v a ∘ s)

pure : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args}
       (v : (arg : _) (pr : arg ∈ args) → lookup pr fs) → Record args fs
pure = mkRecord ∘ [pure]

[pure′] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
         (v : (arg : _) (pr : arg ∈ args) → fs pr) → [Record] args ([tabulate] args fs)
[pure′] {args = lt ■}           v = lift tt
[pure′] {args = hd , lt ∷ args} v = v _ z , [pure′] (λ a → v a ∘ s)

pure′ : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : {arg : _} (pr : arg ∈ args) → Set ℓ}
        (v : (arg : _) (pr : arg ∈ args) → fs pr) → Record args (tabulate fs)
pure′ = mkRecord ∘ [pure′]

-- A special sort of content may be a Fields-morphism: for each
-- field we will explaing how to turn data belonging to the first
-- type of Records to the second one.

infixr 3 _[⟶]_ _⟶_
_[⟶]_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
         (fs : [Fields] ℓᶠ args) (gs : [Fields] ℓᵍ args) → [Fields] (ℓᶠ ⊔ ℓᵍ) args
fs [⟶] gs = [tabulate] _ $ λ pr → [lookup] pr fs → [lookup] pr gs

_⟶_ : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
       (f : Fields ℓᶠ args) (g : Fields ℓᵍ args) → Fields (ℓᶠ ⊔ ℓᵍ) args
fs ⟶ gs = mkFields $ fields fs [⟶] fields gs

-- And given a first record whose fields are Fields-morphism
-- and a second record whose fields are of the corresponding
-- domain, we can apply them in a pointwise manner:

[app] : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
        {fs : [Fields] ℓᶠ args} {gs : [Fields] ℓᵍ args}
        (fs→gs : [Record] args (fs [⟶] gs)) (r : [Record] args fs) → [Record] args gs
[app] {args = lt ■}           fs→gs         fs       = lift tt
[app] {args = hd , lt ∷ args} (f→g , fs→gs) (f , fs) = f→g f , [app] fs→gs fs

app : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
      {fs : Fields ℓᶠ args} {gs : Fields ℓᵍ args}
      (fs→gs : Record args (fs ⟶ gs)) (f : Record args fs) → Record args gs
app fs→gs f = mkRecord $ [app] (content fs→gs) (content f)

[map] : {ℓᶠ ℓᵍ : Level} {lb ub : _} (args : UniqueSortedList lb ub)
        {fs : {arg : _} (pr : arg ∈ args) → Set ℓᶠ}
        {gs : {arg : _} (pr : arg ∈ args) → Set ℓᵍ}
        (fs→gs : {arg : _} (pr : arg ∈ args) → fs pr → gs pr)
        (f : [Record] args ([tabulate] args fs)) → [Record] args ([tabulate] args gs)
[map] (_ ■)          fs→gs f       = lift tt
[map] (_ , _ ∷ args) fs→gs (v , f) = fs→gs z v , [map] args (fs→gs ∘ s) f

map : {ℓᶠ ℓᵍ : Level} {lb ub : _} {args : UniqueSortedList lb ub}
      {fs : {arg : _} (pr : arg ∈ args) → Set ℓᶠ}
      {gs : {arg : _} (pr : arg ∈ args) → Set ℓᵍ}
      (fs→gs : {arg : _} (pr : arg ∈ args) → fs pr → gs pr)
      (f : Record args (tabulate fs)) → Record args (tabulate gs)
map fs→gs = mkRecord ∘ [map] _ fs→gs ∘ content

[seqA] : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : [Fields] ℓ args}
         {a : Set ℓ → Set ℓ} (A : RawApplicative a) →
         [Record] args [ a [ fs ]] → a ([Record] args fs)
[seqA] {ℓ} {args = args} {a = a} A = go args
  where
    module RA = RawApplicative A ; open RA

    go : {lb ub : _} (args : UniqueSortedList lb ub) {fs : [Fields] ℓ args} →
         [Record] args [ a [ fs ]] → a ([Record] args fs)
    go (lt ■)           r        = RA.pure r
    go (hd , lt ∷ args) (av , r) = _,_ RA.<$> av RA.⊛ go args r

seqA : {ℓ : Level} {lb ub : _} {args : UniqueSortedList lb ub} {fs : Fields ℓ args}
       {a : Set ℓ → Set ℓ} (A : RawApplicative a) →
       Record args (a [ fs ]) → a (Record args fs)
seqA A r = mkRecord RA.<$> [seqA] A (content r)
  where module RA = RawApplicative A
