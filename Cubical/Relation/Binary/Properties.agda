{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_; flip; id)

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Definitions

open import Cubical.Relation.Nullary.Decidable

open import Cubical.Data.Maybe using (just; nothing; Dec→Maybe; map-Maybe)
open import Cubical.Data.Sum.Base as Sum using (inl; inr)
open import Cubical.Data.Prod.Base using (_,_)
open import Cubical.Data.Empty using (elim; ⊥; isProp⊥)

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ p : Level
    A : Type a
    B : Type b

------------------------------------------------------------------------
-- Equality properties

≡Reflexive : Reflexive (Path A)
≡Reflexive = refl

≡Symmetric : Symmetric (Path A)
≡Symmetric = sym

≡Transitive : Transitive (Path A)
≡Transitive = _∙_

≡Substitutive : Substitutive (Path A) ℓ
≡Substitutive P = subst P

------------------------------------------------------------------------
-- Implication properties

⇒-refl : Reflexive (_⇒_ {A = A} {B = A} {ℓ = ℓ})
⇒-refl = id

⇒-trans : Trans (_⇒_ {A = A} {B = B} {ℓ = ℓ₁} {ℓ' = ℓ₂}) (_⇒_ {ℓ' = ℓ₃}) _⇒_ -- Transitive _⇒_
⇒-trans f g x = g (f x)

------------------------------------------------------------------------
-- Substitutive properties

module _ (_∼_ : Rel A ℓ₁) (P : Rel A p) where

  subst→respˡ : Substitutive _∼_ p → P Respectsˡ _∼_
  subst→respˡ subst {y} x′∼x Px′y = subst (flip P y) x′∼x Px′y

  subst→respʳ : Substitutive _∼_ p → P Respectsʳ _∼_
  subst→respʳ subst {x} y′∼y Pxy′ = subst (P x) y′∼y Pxy′

  subst→resp₂ : Substitutive _∼_ p → P Respects₂ _∼_
  subst→resp₂ subst = subst→respʳ subst , subst→respˡ subst

module _ {_∼_ : Rel A ℓ} {P : A → Type p} where

  P-resp→¬P-resp : Symmetric _∼_ → P Respects _∼_ → (¬_ ∘ P) Respects _∼_
  P-resp→¬P-resp sym resp x∼y ¬Px Py = ¬Px (resp (sym x∼y) Py)

Respectsʳ≡ : (_∼_ : Rel A ℓ) → _∼_ Respectsʳ _≡_
Respectsʳ≡ _∼_ = subst→respʳ _≡_ _∼_ ≡Substitutive

Respectsˡ≡ : (_∼_ : Rel A ℓ) → _∼_ Respectsˡ _≡_
Respectsˡ≡ _∼_ = subst→respˡ _≡_ _∼_ ≡Substitutive

Respects₂≡ : (_∼_ : Rel A ℓ) → _∼_ Respects₂ _≡_
Respects₂≡ _∼_ = subst→resp₂ _≡_ _∼_ ≡Substitutive

------------------------------------------------------------------------
-- Proofs for non-strict orders

module _ {_≤_ : Rel A ℓ} where

  total→FromEq : Total _≤_ → FromEq _≤_
  total→FromEq total {x} {y} x≡y with total x y
  ... | inl x∼y = x∼y
  ... | inr y∼x = Respectsʳ≡ _≤_ x≡y (Respectsˡ≡ _≤_ (sym x≡y) y∼x)

  total∧dec→dec : FromEq _≤_ → Antisymmetric _≤_ →
                  Total _≤_ → Discrete A → Decidable _≤_
  total∧dec→dec reflx antisym total _≟_ x y with total x y
  ... | inl x≤y = yes x≤y
  ... | inr y≤x = mapDec reflx (flip antisym y≤x) (x ≟ y)
    where
      mapDec : ∀ {A : Type a} {B : Type b} → (A → B) → (B → A) → Dec A → Dec B
      mapDec f g (yes x) = yes (f x)
      mapDec f g (no ¬x) = no (¬x ∘ g)

------------------------------------------------------------------------
-- Proofs for strict orders

module _ {_<_ : Rel A ℓ} where

  trans∧irr→asym : Transitive _<_ → Irreflexive _<_ → Asymmetric _<_
  trans∧irr→asym transitive irrefl x<y y<x = irrefl (transitive x<y y<x)

  irr∧antisym→asym : Irreflexive _<_ → Antisymmetric _<_ → Asymmetric _<_
  irr∧antisym→asym irrefl antisym x<y y<x = irrefl→tonoteq irrefl x<y (antisym x<y y<x)
    where
      irrefl→tonoteq : Irreflexive _<_ → ToNotEq _<_
      irrefl→tonoteq irrefl {x} {y} x<y x≡y = irrefl (subst (λ z → x < z) (sym x≡y) x<y)

  asym→antisym : Asymmetric _<_ → Antisymmetric _<_
  asym→antisym asym x<y y<x = elim (asym x<y y<x)

  asym→irr : Asymmetric _<_ → Irreflexive _<_
  asym→irr asym {x} x<x = asym x<x x<x

  tri→asym : Trichotomous _<_ → Asymmetric _<_
  tri→asym compare {x} {y} x<y x>y with compare x y
  ... | tri< _   _ x≯y = x≯y x>y
  ... | tri≡ _   _ x≯y = x≯y x>y
  ... | tri> x≮y _ _   = x≮y x<y

  tri→irr : Trichotomous _<_ → Irreflexive _<_
  tri→irr compare {x} x<x with compare x x
  ... | tri< _ _ x≮x = x≮x x<x
  ... | tri≡ _ _ x≮x = x≮x x<x
  ... | tri> x≮x _ _ = x≮x x<x

  tri→dec≡ : Trichotomous _<_ → Discrete A
  tri→dec≡ compare x y with compare x y
  ... | tri< _ x≢y _ = no  x≢y
  ... | tri≡ _ x≡y _ = yes x≡y
  ... | tri> _ x≢y _ = no  x≢y

  tri→dec< : Trichotomous _<_ → Decidable _<_
  tri→dec< compare x y with compare x y
  ... | tri< x<y _ _ = yes x<y
  ... | tri≡ x≮y _ _ = no  x≮y
  ... | tri> x≮y _ _ = no  x≮y

------------------------------------------------------------------------
-- Without Loss of Generality

module _ {_R_ : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  wlog : Total _R_ → Symmetric Q →
         (∀ a b → a R b → Q a b) →
         ∀ a b → Q a b
  wlog r-total q-sym prf a b with r-total a b
  ... | inl aRb = prf a b aRb
  ... | inr bRa = q-sym (prf b a bRa)

------------------------------------------------------------------------
-- Other proofs

module _ {P : REL A B p} where

  dec→weaklyDec : Decidable P → WeaklyDecidable P
  dec→weaklyDec dec x y = Dec→Maybe (dec x y)

module _ {P : Rel A ℓ₁} {Q : Rel A ℓ₂} (f : P ⇒ Q) where

  map-Reflexive : Reflexive P → Reflexive Q
  map-Reflexive reflx = f reflx

  map-FromEq : FromEq P → FromEq Q
  map-FromEq fromEq p = f (fromEq p)

  cmap-Irreflexive : Irreflexive Q → Irreflexive P
  cmap-Irreflexive irrefl x≡x = irrefl (f x≡x)

  cmap-ToNotEq : ToNotEq Q → ToNotEq P
  cmap-ToNotEq toNotEq x = toNotEq (f x)


module _ {P : REL A B ℓ₁} {Q : REL A B ℓ₂} (f : P ⇒ Q) where

  map-Universal : Universal P → Universal Q
  map-Universal u x y = f (u x y)

  map-NonEmpty : NonEmpty P → NonEmpty Q
  map-NonEmpty x = nonEmpty (f (NonEmpty.proof x))


module _ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} where

  flip-Connex : Connex P Q → Connex Q P
  flip-Connex f x y = Sum.swap (f y x)

module _ (_∼_ : Rel A ℓ) where

  reflx→fromeq : Reflexive _∼_ → FromEq _∼_
  reflx→fromeq reflx {x} = J (λ z _ → x ∼ z) reflx

  fromeq→reflx : FromEq _∼_ → Reflexive _∼_
  fromeq→reflx fromEq = fromEq refl

  irrefl→tonoteq : Irreflexive _∼_ → ToNotEq _∼_
  irrefl→tonoteq irrefl {x} {y} x<y x≡y = irrefl (subst (λ z → x ∼ z) (sym x≡y) x<y)

  tonoteq→irrefl : ToNotEq _∼_ → Irreflexive _∼_
  tonoteq→irrefl toNotEq x<x = toNotEq x<x refl

------------------------------------------------------------------------
-- Proofs for propositional relations (PropRel)

isPropIsPropValued : {R : REL A B ℓ} → isProp (isPropValued R)
isPropIsPropValued a b i x y = isPropIsProp (a x y) (b x y) i

module _ {R : Rel A ℓ} (propR : isPropValued R) where

  isPropReflexive : isProp (Reflexive R)
  isPropReflexive a b i {x} = propR x x a b i

  isPropFromEq : isProp (FromEq R)
  isPropFromEq a b i {x} {y} p = propR x y (a p) (b p) i

  isPropIrreflexive : isProp (Irreflexive R)
  isPropIrreflexive a b i {x} xRx = isProp⊥ (a xRx) (b xRx) i

  isPropToNotEq : isProp (ToNotEq R)
  isPropToNotEq a b i {x} {y} xRy x≡y = isProp⊥ (a xRy x≡y) (b xRy x≡y) i

  isPropAsymmetric : isProp (Asymmetric R)
  isPropAsymmetric a b i {x} {y} xRy yRx = isProp⊥ (a xRy yRx) (b xRy yRx) i

isProp⇒ : {R : REL A B ℓ₁} {Q : REL A B ℓ₂} → isPropValued Q → isProp (R ⇒ Q)
isProp⇒ propQ a b i {x} {y} xRy = propQ x y (a xRy) (b xRy) i

isPropSym : {R : REL A B ℓ₁} {Q : REL B A ℓ₂} → isPropValued Q → isProp (Sym R Q)
isPropSym propQ = isProp⇒ (flip propQ)

isPropTrans : ∀ {c} {C : Type c}
                      {P : REL A B ℓ₁} {Q : REL B C ℓ₂} {R : REL A C ℓ₃} →
                      isPropValued R → isProp (Trans P Q R)
isPropTrans propR a b i {x} {_} {z} xPy yQz = propR x z (a xPy yQz) (b xPy yQz) i

-- If E = _≡_, then isSet A can be used in place of isPropValued E
isPropAntisym : {R : REL A B ℓ₁} {Q : REL B A ℓ₂} {E : REL A B ℓ₃} → isPropValued E → isProp (Antisym R Q E)
isPropAntisym propE a b i {x} {y} xRy yQx = propE x y (a xRy yQx) (b xRy yQx) i

module _ {R : REL A B ℓ} (propR : isPropValued R) where

  Universal→isContrValued : Universal R → ∀ {a b} → isContr (R a b)
  Universal→isContrValued univr {a} {b} = univr a b , propR a b _
