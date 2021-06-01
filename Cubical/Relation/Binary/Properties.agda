{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_; _$_; flip; id)
open import Cubical.Foundations.Logic hiding (_⇒_; _⇔_) renaming (⇔toPath to hProp⇔toPath)

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Definitions

open import Cubical.Relation.Nullary.Decidable hiding (¬_)

open import Cubical.Data.Maybe using (just; nothing; Dec→Maybe; map-Maybe)
open import Cubical.Data.Sum.Base as Sum using (inl; inr)
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (elim to ⊥-elim)
open import Cubical.HITs.PropositionalTruncation

private
  variable
    a b ℓ ℓ₁ ℓ₂ ℓ₃ p : Level
    A : Type a
    B : Type b

------------------------------------------------------------------------
-- Equality properties

≡ₚReflexive : Reflexive (_≡ₚ_ {A = A})
≡ₚReflexive = ∣ refl ∣

≡ₚSymmetric : Symmetric (_≡ₚ_ {A = A})
≡ₚSymmetric = map sym

≡ₚTransitive : Transitive (_≡ₚ_ {A = A})
≡ₚTransitive = map2 _∙_

≡ₚSubstitutive : Substitutive (_≡ₚ_ {A = A}) ℓ
≡ₚSubstitutive P = elim (λ _ → isPropΠ λ _ → P _ .snd) (subst (λ x → P x .fst))

------------------------------------------------------------------------
-- Substitutive properties

module _ (_∼_ : Rel A ℓ₁) (P : Rel A p) where

  subst→respˡ : Substitutive _∼_ p → P Respectsˡ _∼_
  subst→respˡ subst {y} x′∼x Px′y = subst (flip P y) x′∼x Px′y

  subst→respʳ : Substitutive _∼_ p → P Respectsʳ _∼_
  subst→respʳ subst {x} y′∼y Pxy′ = subst (P x) y′∼y Pxy′

  subst→resp₂ : Substitutive _∼_ p → P Respects₂ _∼_
  subst→resp₂ subst = subst→respʳ subst , subst→respˡ subst

module _ (_∼_ : Rel A ℓ) (P : A → hProp p) where

  P-resp→¬P-resp : Symmetric _∼_ → P Respects _∼_ → (¬_ ∘ P) Respects _∼_
  P-resp→¬P-resp sym resp x∼y ¬Px Py = ¬Px (resp (sym x∼y) Py)

Respectsʳ≡ₚ : (_∼_ : Rel A ℓ) → _∼_ Respectsʳ _≡ₚ_
Respectsʳ≡ₚ _∼_ = subst→respʳ _≡ₚ_ _∼_ ≡ₚSubstitutive

Respectsˡ≡ₚ : (_∼_ : Rel A ℓ) → _∼_ Respectsˡ _≡ₚ_
Respectsˡ≡ₚ _∼_ = subst→respˡ _≡ₚ_ _∼_ ≡ₚSubstitutive

Respects₂≡ₚ : (_∼_ : Rel A ℓ) → _∼_ Respects₂ _≡ₚ_
Respects₂≡ₚ _∼_ = subst→resp₂ _≡ₚ_ _∼_ ≡ₚSubstitutive

------------------------------------------------------------------------
-- Proofs for non-strict orders

module _ (_≤_ : Rel A ℓ) where

  rawtotal→FromEq : RawTotal _≤_ → FromEq _≤_
  rawtotal→FromEq total {x} {y} x≡y with total x y
  ... | inl x∼y = x∼y
  ... | inr y∼x = Respectsʳ≡ₚ _≤_ x≡y (Respectsˡ≡ₚ _≤_ (≡ₚSymmetric x≡y) y∼x)

  total→FromEq : Total _≤_ → FromEq _≤_
  total→FromEq total {x} {y} x≡y = elim (λ _ → (x ≤ y) .snd)
    (λ {
      (inl x∼y) → x∼y
    ; (inr y∼x) → Respectsʳ≡ₚ _≤_ x≡y (Respectsˡ≡ₚ _≤_ (≡ₚSymmetric x≡y) y∼x)
    }) (total x y)


------------------------------------------------------------------------
-- Proofs for strict orders

module _ (_<_ : Rel A ℓ) where

  trans∧irr→asym : Transitive _<_ → Irreflexive _<_ → Asymmetric _<_
  trans∧irr→asym transitive irrefl x<y y<x = irrefl (transitive x<y y<x)

  irr∧antisym→asym : Irreflexive _<_ → Antisymmetric _<_ → Asymmetric _<_
  irr∧antisym→asym irrefl antisym x<y y<x = irrefl→tonoteq irrefl x<y (antisym x<y y<x)
    where
      irrefl→tonoteq : Irreflexive _<_ → ToNotEq _<_
      irrefl→tonoteq irrefl {x} {y} x<y x≡y = irrefl (substₚ (λ z → x < z) (≡ₚSymmetric x≡y) x<y)

  asym→antisym : Asymmetric _<_ → Antisymmetric _<_
  asym→antisym asym x<y y<x = ⊥-elim (asym x<y y<x)

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

module _ {R : Rel A ℓ₁} {Q : Rel A ℓ₂} where

  wlog : Total R → Symmetric Q →
         R ⇒ Q → Universal Q
  wlog r-total q-sym prf a b = elim (λ _ → Q a b .snd)
    (λ {
      (inl Rab) → prf Rab
    ; (inr Rba) → q-sym (prf Rba)
    }) (r-total a b)


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
  map-NonEmpty = map (λ (x , p) → x , map (λ (y , q) → y , f q) p)


module _ {P : REL A B ℓ₁} {Q : REL B A ℓ₂} where

  flip-RawConnex : RawConnex P Q → RawConnex Q P
  flip-RawConnex f x y = Sum.swap (f y x)

  flip-Connex : Connex P Q → Connex Q P
  flip-Connex f x y = map Sum.swap (f y x)

module _ (_∼_ : Rel A ℓ) where

  reflx→fromeq : Reflexive _∼_ → FromEq _∼_
  reflx→fromeq reflx {x} p = substₚ (x ∼_) p reflx

  fromeq→reflx : FromEq _∼_ → Reflexive _∼_
  fromeq→reflx fromEq = fromEq ∣ refl ∣

  irrefl→tonoteq : Irreflexive _∼_ → ToNotEq _∼_
  irrefl→tonoteq irrefl {x} {y} x<y x≡y = irrefl (substₚ (x ∼_) (≡ₚSymmetric x≡y) x<y)

  tonoteq→irrefl : ToNotEq _∼_ → Irreflexive _∼_
  tonoteq→irrefl toNotEq x<x = toNotEq x<x ∣ refl ∣

------------------------------------------------------------------------
-- Proofs for propositional relations only

isPropIsPropValued : {R : RawREL A B ℓ} → isProp (isPropValued R)
isPropIsPropValued a b i x y = isPropIsProp (a x y) (b x y) i

module _ (R : Rel A ℓ) where

  isPropReflexive : isProp (Reflexive R)
  isPropReflexive a b i {x} = R x x .snd a b i

  isPropFromEq : isProp (FromEq R)
  isPropFromEq a b i {x} {y} p = R x y .snd (a p) (b p) i

  isPropIrreflexive : isProp (Irreflexive R)
  isPropIrreflexive a b i {x} xRx = isProp⊥ (a xRx) (b xRx) i

  isPropToNotEq : isProp (ToNotEq R)
  isPropToNotEq a b i {x} {y} xRy x≡y = isProp⊥ (a xRy x≡y) (b xRy x≡y) i

  isPropAsymmetric : isProp (Asymmetric R)
  isPropAsymmetric a b i {x} {y} xRy yRx = isProp⊥ (a xRy yRx) (b xRy yRx) i

isProp⇒ : (R : REL A B ℓ₁) (Q : REL A B ℓ₂) → isProp (R ⇒ Q)
isProp⇒ R Q a b i {x} {y} xRy = Q x y .snd (a xRy) (b xRy) i

isPropSym : (R : REL A B ℓ₁) (Q : REL B A ℓ₂) → isProp (Sym R Q)
isPropSym R Q = isProp⇒ R (flip Q)

isPropTrans : ∀ {c} {C : Type c}
                      (P : REL A B ℓ₁) (Q : REL B C ℓ₂) (R : REL A C ℓ₃) →
                      isProp (Trans P Q R)
isPropTrans P Q R a b i {x} {_} {z} xPy yQz = R x z .snd (a xPy yQz) (b xPy yQz) i

isPropAntisym : (R : REL A B ℓ₁) (Q : REL B A ℓ₂) (E : REL A B ℓ₃) → isProp (Antisym R Q E)
isPropAntisym R Q E a b i {x} {y} xRy yQx = E x y .snd (a xRy yQx) (b xRy yQx) i

module _ (R : REL A B ℓ) where

  Universal→isContrValued : Universal R → ∀ {a b} → isContr ⟨ R a b ⟩
  Universal→isContrValued univr {a} {b} = univr a b , R a b .snd _


------------------------------------------------------------------------
-- Bidirectional implication and equality

⇔toPath : {R : REL A B ℓ} {Q : REL A B ℓ} → R ⇔ Q → R ≡ Q
⇔toPath (R⇒Q , Q⇒R) = funExt (λ x → funExt (λ y → hProp⇔toPath R⇒Q Q⇒R))
