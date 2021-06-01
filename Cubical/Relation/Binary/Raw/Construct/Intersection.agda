{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Relation.Binary.Raw.Construct.Intersection where

open import Cubical.Core.Everything
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Prod
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr; rec)
open import Cubical.Relation.Binary.Raw
open import Cubical.Relation.Nullary using (yes; no)

------------------------------------------------------------------------
-- Definition

_∩_ : ∀ {a b ℓ₁ ℓ₂} {A : Type a} {B : Type b} →
      RawREL A B ℓ₁ → RawREL A B ℓ₂ → RawREL A B (ℓ-max ℓ₁ ℓ₂)
L ∩ R = λ i j → L i j × R i j

------------------------------------------------------------------------
-- Properties

module _ {a ℓ₁ ℓ₂} {A : Type a} (L : RawRel A ℓ₁) (R : RawRel A ℓ₂) where

  reflexive : Reflexive L → Reflexive R → Reflexive (L ∩ R)
  reflexive L-refl R-refl = L-refl , R-refl

  symmetric : Symmetric L → Symmetric R → Symmetric (L ∩ R)
  symmetric L-sym R-sym = map L-sym R-sym

  transitive : Transitive L → Transitive R → Transitive (L ∩ R)
  transitive L-trans R-trans (xLy , xRy) (yLz , yRz) = L-trans xLy yLz , R-trans xRy yRz

  respects : ∀ {p} (P : A → Type p) →
             P Respects L ⊎ P Respects R → P Respects (L ∩ R)
  respects P resp (Lxy , Rxy) = rec (λ x → x Lxy) (λ x → x Rxy) resp

  min : ∀ {⊤} → Minimum L ⊤ → Minimum R ⊤ → Minimum (L ∩ R) ⊤
  min L-min R-min = intro L-min R-min

  max : ∀ {⊥} → Maximum L ⊥ → Maximum R ⊥ → Maximum (L ∩ R) ⊥
  max L-max R-max = intro L-max R-max

  toNotEq : ToNotEq L ⊎ ToNotEq R → ToNotEq (L ∩ R)
  toNotEq tonoteq (Lxy , Rxy) x≡y = rec (λ x → x Lxy x≡y) (λ y → y Rxy x≡y) tonoteq

  irreflexive : Irreflexive L ⊎ Irreflexive R → Irreflexive (L ∩ R)
  irreflexive irrefl (xLx , xRx) = rec (λ x → x xLx) (λ y → y xRx) irrefl

  antisymmetric : Antisymmetric L ⊎ Antisymmetric R → Antisymmetric (L ∩ R)
  antisymmetric (inl L-antisym) (Lxy , _) (Lyx , _) = L-antisym Lxy Lyx
  antisymmetric (inr R-antisym) (_ , Rxy) (_ , Ryx) = R-antisym Rxy Ryx

module _ {a b ℓ₁ ℓ₂ ℓ₃} {A : Type a} {B : Type b}
         (≈ : RawREL A B ℓ₁) {L : RawREL A B ℓ₂} {R : RawREL A B ℓ₃} where

  implies : (≈ ⇒ L) → (≈ ⇒ R) → ≈ ⇒ (L ∩ R)
  implies ≈⇒L ≈⇒R = intro ≈⇒L ≈⇒R

module _ {a ℓ₁ ℓ₂ ℓ₃} {A : Type a}
         (≈ : RawRel A ℓ₁) (L : RawRel A ℓ₂) (R : RawRel A ℓ₃) where

  respectsˡ : L Respectsˡ ≈ → R Respectsˡ ≈ → (L ∩ R) Respectsˡ ≈
  respectsˡ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respectsʳ : L Respectsʳ ≈ → R Respectsʳ ≈ → (L ∩ R) Respectsʳ ≈
  respectsʳ L-resp R-resp x≈y = map (L-resp x≈y) (R-resp x≈y)

  respects₂ : L Respects₂ ≈ → R Respects₂ ≈ → (L ∩ R) Respects₂ ≈
  respects₂ (Lʳ , Lˡ) (Rʳ , Rˡ) = respectsʳ Lʳ Rʳ , respectsˡ Lˡ Rˡ

module _ {a b ℓ₁ ℓ₂} {A : Type a} {B : Type b} {L : RawREL A B ℓ₁} {R : RawREL A B ℓ₂} where

  decidable : Decidable L → Decidable R → Decidable (L ∩ R)
  decidable L? R? x y = ×-dec (L? x y) (R? x y)

------------------------------------------------------------------------
-- Structures

module _ {a ℓ₁ ℓ₂} {A : Type a} {L : RawRel A ℓ₁} {R : RawRel A ℓ₂} where

  isPartialEquivalence : IsPartialEquivalence L → IsPartialEquivalence R → IsPartialEquivalence (L ∩ R)
  isPartialEquivalence eqₗ eqᵣ = record
    { symmetric  = symmetric  L R Eqₗ.symmetric  Eqᵣ.symmetric
    ; transitive = transitive L R Eqₗ.transitive Eqᵣ.transitive
    }
    where module Eqₗ = IsPartialEquivalence eqₗ; module Eqᵣ = IsPartialEquivalence eqᵣ

  isEquivalence : IsEquivalence L → IsEquivalence R → IsEquivalence (L ∩ R)
  isEquivalence eqₗ eqᵣ = record
    { isPartialEquivalence = isPartialEquivalence Eqₗ.isPartialEquivalence Eqᵣ.isPartialEquivalence
    ; reflexive            = reflexive L R Eqₗ.reflexive Eqᵣ.reflexive
    }
    where module Eqₗ = IsEquivalence eqₗ; module Eqᵣ = IsEquivalence eqᵣ

  isDecEquivalence : IsDecEquivalence L → IsDecEquivalence R → IsDecEquivalence (L ∩ R)
  isDecEquivalence eqₗ eqᵣ = record
    { isEquivalence = isEquivalence Eqₗ.isEquivalence Eqᵣ.isEquivalence
    ; _≟_           = decidable Eqₗ._≟_ Eqᵣ._≟_
    }
    where module Eqₗ = IsDecEquivalence eqₗ; module Eqᵣ = IsDecEquivalence eqᵣ

  isPreorder : IsPreorder L → IsPreorder R → IsPreorder (L ∩ R)
  isPreorder Oₗ Oᵣ = record
    { reflexive  = reflexive L R Oₗ.reflexive Oᵣ.reflexive
    ; transitive = transitive L R Oₗ.transitive Oᵣ.transitive
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderˡ : IsPartialOrder L → IsPreorder R → IsPartialOrder (L ∩ R)
  isPartialOrderˡ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ.isPreorder Oᵣ
    ; antisym    = antisymmetric L R (inl Oₗ.antisym)
    }
    where module Oₗ = IsPartialOrder Oₗ; module Oᵣ = IsPreorder Oᵣ

  isPartialOrderʳ : IsPreorder L → IsPartialOrder R → IsPartialOrder (L ∩ R)
  isPartialOrderʳ Oₗ Oᵣ = record
    { isPreorder = isPreorder Oₗ Oᵣ.isPreorder
    ; antisym    = antisymmetric L R (inr Oᵣ.antisym)
    }
    where module Oₗ = IsPreorder Oₗ; module Oᵣ = IsPartialOrder Oᵣ

  isStrictPartialOrderˡ : IsStrictPartialOrder L → Transitive R → IsStrictPartialOrder (L ∩ R)
  isStrictPartialOrderˡ Oₗ transitiveᵣ = record
    { irrefl     = irreflexive L R (inl Oₗ.irrefl)
    ; transitive = transitive L R Oₗ.transitive transitiveᵣ
    }
    where module Oₗ = IsStrictPartialOrder Oₗ

  isStrictPartialOrderʳ : Transitive L → IsStrictPartialOrder R → IsStrictPartialOrder (L ∩ R)
  isStrictPartialOrderʳ transitiveₗ Oᵣ = record
    { irrefl     = irreflexive L R (inr Oᵣ.irrefl)
    ; transitive = transitive L R transitiveₗ Oᵣ.transitive
    }
    where module Oᵣ = IsStrictPartialOrder Oᵣ
