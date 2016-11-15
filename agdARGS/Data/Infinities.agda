module agdARGS.Data.Infinities where

open import Level
open import Function
open import Data.Product
open import Data.Sum
open import agdARGS.Relation.Nullary
open import Relation.Nullary
open import Relation.Binary

infix 10 ↑_
data [_] {ℓᵃ} (A : Set ℓᵃ) : Set ℓᵃ where
  -∞ : [ A ]
  ↑_ : (a : A) → [ A ]
  +∞ : [ A ]

infix 10 -∞≤_ _≤+∞
data [≤] {ℓᵃ ℓʳ} {A : Set ℓᵃ} (_≤_ : Rel A ℓʳ) :
     (a b : [ A ]) → Set ℓʳ where
  -∞≤_ : (a : [ A ])            → [≤] _≤_ -∞ a
  ↑_   : {a b : A} (le : a ≤ b) → [≤] _≤_ (↑ a) (↑ b)
  _≤+∞ : (a : [ A ])            → [≤] _≤_ a +∞

data [<] {ℓᵃ ℓʳ} {A : Set ℓᵃ} (_<_ : Rel A ℓʳ) :
     (a b : [ A ]) → Set ℓʳ where
  -∞<↑_ : (a : A)                → [<] _<_ -∞ (↑ a)
  -∞<+∞ :                          [<] _<_ -∞ +∞
  ↑_<+∞ : (a : A)                → [<] _<_ (↑ a) +∞
  ↑_    : {a b : A} (lt : a < b) → [<] _<_ (↑ a) (↑ b)

data [≈] {ℓᵃ ℓᵉ} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) :
     (a b : [ A ]) → Set ℓᵉ where
  -∞≈-∞ :                          [≈] _≈_ -∞ -∞
  ↑_    : {a b : A} (eq : a ≈ b) → [≈] _≈_ (↑ a) (↑ b)
  +∞≈+∞ :                          [≈] _≈_ +∞ +∞

IsEquivalenceT : 
  {ℓᵃ ℓᵉ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ)
  (IE : IsEquivalence _≈_) → IsEquivalence ([≈] _≈_)
IsEquivalenceT _≈_ IE =
  record { refl  = refl
         ; sym   = sym
         ; trans = trans }
  where
    refl : Reflexive ([≈] _≈_)
    refl { -∞} = -∞≈-∞
    refl {↑ a} = ↑ IsEquivalence.refl IE
    refl { +∞} = +∞≈+∞

    sym : Symmetric ([≈] _≈_)
    sym -∞≈-∞  = -∞≈-∞
    sym (↑ eq) = ↑ IsEquivalence.sym IE eq
    sym +∞≈+∞  = +∞≈+∞

    trans : Transitive ([≈] _≈_)
    trans -∞≈-∞   eq₂     = eq₂
    trans (↑ eq₁) (↑ eq₂) = ↑ IsEquivalence.trans IE eq₁ eq₂
    trans +∞≈+∞   +∞≈+∞   = +∞≈+∞

IsPreorderT : 
  {ℓᵃ ℓᵉ ℓʳ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) (_≤_ : Rel A ℓʳ)
  (IPO : IsPreorder _≈_ _≤_) → IsPreorder ([≈] _≈_) ([≤] _≤_)
IsPreorderT _≈_ _≤_ IPO =
  record { isEquivalence = IsEquivalenceT _≈_ $ IsPreorder.isEquivalence IPO
         ; reflexive     = reflexive
         ; trans         = trans }
  where
    reflexive : [≈] _≈_ ⇒ [≤] _≤_
    reflexive -∞≈-∞  = -∞≤ -∞
    reflexive (↑ eq) = ↑ IsPreorder.reflexive IPO eq
    reflexive +∞≈+∞  = +∞ ≤+∞

    trans : Transitive ([≤] _≤_)
    trans (-∞≤ a) le₂       = -∞≤ _
    trans (↑ le₁) (↑ le₂)   = ↑ IsPreorder.trans IPO le₁ le₂
    trans (↑ le)  (._ ≤+∞)  = _ ≤+∞
    trans (a ≤+∞) (.+∞ ≤+∞) = a ≤+∞

IsPartialOrderT :
  {ℓᵃ ℓᵉ ℓʳ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) (_≤_ : Rel A ℓʳ)
  (IPO : IsPartialOrder _≈_ _≤_) → IsPartialOrder ([≈] _≈_) ([≤] _≤_)
IsPartialOrderT _≈_ _≤_ IPO =
  record { isPreorder = IsPreorderT _≈_ _≤_ $ IsPartialOrder.isPreorder IPO
         ; antisym    = antisym } 
  where
    antisym : Antisymmetric ([≈] _≈_) ([≤] _≤_)
    antisym (-∞≤ .-∞) (-∞≤ .-∞) = -∞≈-∞
    antisym (↑ le₁)   (↑ le₂)   = ↑ IsPartialOrder.antisym IPO le₁ le₂
    antisym (.+∞ ≤+∞) (.+∞ ≤+∞) = +∞≈+∞

IsTotalOrderT :
  {ℓᵃ ℓᵉ ℓʳ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) (_≤_ : Rel A ℓʳ)
  (ITO : IsTotalOrder _≈_ _≤_) → IsTotalOrder ([≈] _≈_) ([≤] _≤_)
IsTotalOrderT _≈_ _≤_ ITO =
  record { isPartialOrder = IsPartialOrderT _≈_ _≤_ $ IsTotalOrder.isPartialOrder ITO
         ; total          = total }
  where
    total : Total ([≤] _≤_)
    total -∞    b     = inj₁ $ -∞≤ b
    total a     +∞    = inj₁ $ a ≤+∞
    total +∞    b     = inj₂ $ b ≤+∞
    total a     -∞    = inj₂ $ -∞≤ a
    total (↑ a) (↑ b) = [ inj₁ ∘ ↑_ , inj₂ ∘ ↑_ ]′ (IsTotalOrder.total ITO a b)

IsDecTotalOrderT : 
  {ℓᵃ ℓᵉ ℓʳ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) (_≤_ : Rel A ℓʳ)
  (IDTO : IsDecTotalOrder _≈_ _≤_) → IsDecTotalOrder ([≈] _≈_) ([≤] _≤_)
IsDecTotalOrderT {A = A} _≈_ _≤_ IDTO =
  record { isTotalOrder = IsTotalOrderT _≈_ _≤_ $ IsDecTotalOrder.isTotalOrder IDTO
         ; _≟_          = _≟_
         ; _≤?_         = _≤?_ }
  where
    ↑≈-inj : ∀ {a b : A} → [≈] _≈_ (↑ a) (↑ b) → a ≈ b
    ↑≈-inj (↑ eq) = eq

    _≟_ : Decidable ([≈] _≈_)
    -∞    ≟ -∞    = yes -∞≈-∞
    (↑ a) ≟ (↑ b) = dec (IsDecTotalOrder._≟_ IDTO a b) (yes ∘ ↑_) (λ ¬eq → no $ ¬eq ∘ ↑≈-inj)
    +∞    ≟ +∞    = yes +∞≈+∞
    -∞    ≟ (↑ a) = no $ λ ()
    -∞    ≟ +∞    = no $ λ ()
    (↑ a) ≟ -∞    = no $ λ ()
    (↑ a) ≟ +∞    = no $ λ ()
    +∞    ≟ -∞    = no $ λ ()
    +∞    ≟ (↑ a) = no $ λ ()

    ↑≤-inj : ∀ {a b : A} → [≤] _≤_ (↑ a) (↑ b) → a ≤ b
    ↑≤-inj (↑ le) = le

    _≤?_ : Decidable ([≤] _≤_)
    -∞    ≤? b     = yes $ -∞≤ b
    (↑ a) ≤? (↑ b) = dec (IsDecTotalOrder._≤?_ IDTO a b) (yes ∘ ↑_) (λ ¬le → no $ ¬le ∘ ↑≤-inj)
    a     ≤? +∞    = yes $ a ≤+∞
    (↑ a) ≤? -∞    = no $ λ ()
    +∞    ≤? -∞    = no $ λ ()
    +∞    ≤? (↑ a) = no $ λ ()

IsStrictTotalOrderT : 
  {ℓᵃ ℓᵉ ℓʳ : Level} {A : Set ℓᵃ} (_≈_ : Rel A ℓᵉ) (_<_ : Rel A ℓʳ)
  (ISTO : IsStrictTotalOrder _≈_ _<_) → IsStrictTotalOrder ([≈] _≈_) ([<] _<_)
IsStrictTotalOrderT _≈_ _<_ ISTO =
  record { isEquivalence         = IsEquivalenceT _≈_ $ IsStrictTotalOrder.isEquivalence ISTO
         ; trans                 = trans
         ; compare               = compare
         }
  where

    trans : Transitive ([<] _<_)
    trans (-∞<↑ a) ↑ .a <+∞ = -∞<+∞
    trans (-∞<↑ a) (↑ lt₂)  = -∞<↑ _
    trans -∞<+∞    ()
    trans ↑ a <+∞  ()
    trans (↑ lt₁)  ↑ b <+∞  = ↑ _ <+∞
    trans (↑ lt₁)  (↑ lt₂)  = ↑ IsStrictTotalOrder.trans ISTO lt₁ lt₂

    ↑≈-inj : ∀ {a b : _} → [≈] _≈_ (↑ a) (↑ b) → a ≈ b
    ↑≈-inj (↑ eq) = eq

    ↑<-inj : ∀ {a b : _} → [<] _<_ (↑ a) (↑ b) → a < b
    ↑<-inj (↑ lt) = lt

    compare : Trichotomous ([≈] _≈_) ([<] _<_)
    compare -∞    -∞    = tri≈ (λ ()) -∞≈-∞ (λ ())
    compare -∞    (↑ a) = tri< (-∞<↑ a) (λ ()) (λ ())
    compare -∞    +∞    = tri< -∞<+∞ (λ ()) (λ ())
    compare (↑ a) -∞    = tri> (λ ()) (λ ()) (-∞<↑ a)
    compare (↑ a) (↑ b) with IsStrictTotalOrder.compare ISTO a b
    ... | tri< lt ¬b ¬c = tri< (↑ lt)        (¬b ∘ ↑≈-inj) (¬c ∘ ↑<-inj)
    ... | tri≈ ¬a eq ¬c = tri≈ (¬a ∘ ↑<-inj) (↑ eq)        (¬c ∘ ↑<-inj)
    ... | tri> ¬a ¬b gt = tri> (¬a ∘ ↑<-inj) (¬b ∘ ↑≈-inj) (↑ gt)
    compare (↑ a) +∞    = tri< ↑ a <+∞ (λ ()) (λ ())
    compare +∞    -∞    = tri> (λ ()) (λ ()) -∞<+∞
    compare +∞    (↑ a) = tri> (λ ()) (λ ()) ↑ a <+∞
    compare +∞    +∞    = tri≈ (λ ()) +∞≈+∞ (λ ())

PosetT : {ℓᵃ ℓᵉ ℓʳ : Level} → Poset ℓᵃ ℓᵉ ℓʳ → Poset ℓᵃ ℓᵉ ℓʳ
PosetT PO =
  record { Carrier        = _
         ; _≈_            = _
         ; _≤_            = _
         ; isPartialOrder = IsPartialOrderT _ _ $ Poset.isPartialOrder PO }


TotalOrderT : {ℓᵃ ℓᵉ ℓʳ : Level} → TotalOrder ℓᵃ ℓᵉ ℓʳ → TotalOrder ℓᵃ ℓᵉ ℓʳ
TotalOrderT TO =
  record { Carrier      = _
         ; _≈_          = _
         ; _≤_          = _
         ; isTotalOrder = IsTotalOrderT _ _ $ TotalOrder.isTotalOrder TO }

DecTotalOrderT : {ℓᵃ ℓᵉ ℓʳ : Level} → DecTotalOrder ℓᵃ ℓᵉ ℓʳ → DecTotalOrder ℓᵃ ℓᵉ ℓʳ
DecTotalOrderT DTO =
  record { Carrier         = _
         ; _≈_             = _ 
         ; _≤_             = _ 
         ; isDecTotalOrder = IsDecTotalOrderT _ _ $ DecTotalOrder.isDecTotalOrder DTO }

StrictTotalOrderT : {ℓᵃ ℓᵉ ℓʳ : Level} → StrictTotalOrder ℓᵃ ℓᵉ ℓʳ → StrictTotalOrder ℓᵃ ℓᵉ ℓʳ
StrictTotalOrderT STO = 
  record { Carrier            = _
         ; _≈_                = _ 
         ; _<_                = _ 
         ; isStrictTotalOrder = IsStrictTotalOrderT _ _ $ StrictTotalOrder.isStrictTotalOrder STO }
