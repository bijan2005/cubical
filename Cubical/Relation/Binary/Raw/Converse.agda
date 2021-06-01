{-# OPTIONS --cubical --without-K --safe #-}
module Cubical.Relation.Binary.Raw.Converse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Prod

open import Cubical.Relation.Binary.Raw

------------------------------------------------------------------------
-- Properties

module _ {a ℓ} {A : Set a} (∼ : RawRel A ℓ) where

  reflexive : Reflexive ∼ → Reflexive (flip ∼)
  reflexive r = r

  irrefl : Irreflexive ∼ → Irreflexive (flip ∼)
  irrefl i = i

  symmetric : Symmetric ∼ → Symmetric (flip ∼)
  symmetric s = s

  transitive : Transitive ∼ → Transitive (flip ∼)
  transitive t = flip t

  asym : Asymmetric ∼ → Asymmetric (flip ∼)
  asym a = a

  total : Total ∼ → Total (flip ∼)
  total t x y = t y x

  totalₚ : PropTotal ∼ → PropTotal (flip ∼)
  totalₚ t x y = t y x

  resp : ∀ {p} (P : A → Set p) → Symmetric ∼ →
             P Respects ∼ → P Respects (flip ∼)
  resp _ sym resp ∼ = resp (sym ∼)

  max : ∀ {⊥} → Minimum ∼ ⊥ → Maximum (flip ∼) ⊥
  max min = min

  min : ∀ {⊤} → Maximum ∼ ⊤ → Minimum (flip ∼) ⊤
  min max = max

  fromEq : FromEq ∼ → FromEq (flip ∼)
  fromEq impl = impl ∘ sym

  toNotEq : ToNotEq ∼ → ToNotEq (flip ∼)
  toNotEq tne y∼x x≡y = tne y∼x (sym x≡y)

  antisym : Antisymmetric ∼ → Antisymmetric (flip ∼)
  antisym ans = flip ans

  compare : Trichotomous ∼ → Trichotomous (flip ∼)
  compare cmp x y with cmp x y
  ... | tri< x<y x≡y y≮x = tri> y≮x x≡y x<y
  ... | tri≡ x≮y x≡y y≮x = tri≡ y≮x x≡y x≮y
  ... | tri> x≮y x≡y y<x = tri< y<x x≡y x≮y

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : RawRel A ℓ₁) (∼₂ : RawRel A ℓ₂) where

  resp₂ : ∼₁ Respects₂ ∼₂ → (flip ∼₁) Respects₂ ∼₂
  resp₂ (resp₁ , resp₂) = resp₂ , resp₁

module _ {a b ℓ} {A : Set a} {B : Set b} (∼ : RawREL A B ℓ) where

  dec : Decidable ∼ → Decidable (flip ∼)
  dec dec = flip dec

------------------------------------------------------------------------
-- Structures

module _ {a ℓ} {A : Set a} {≈ : RawRel A ℓ} where

  isPartialEquivalence : IsPartialEquivalence ≈ → IsPartialEquivalence (flip ≈)
  isPartialEquivalence eq = record
    { symmetric  = symmetric  ≈ Eq.symmetric
    ; transitive = transitive ≈ Eq.transitive
    }
    where module Eq = IsPartialEquivalence eq

  isEquivalence : IsEquivalence ≈ → IsEquivalence (flip ≈)
  isEquivalence eq = record
    { isPartialEquivalence = isPartialEquivalence Eq.isPartialEquivalence
    ; reflexive            = reflexive ≈ Eq.reflexive
    }
    where module Eq = IsEquivalence eq

  isDecEquivalence : IsDecEquivalence ≈ → IsDecEquivalence (flip ≈)
  isDecEquivalence eq = record
    { isEquivalence = isEquivalence Dec.isEquivalence
    ; _≟_           = dec ≈ Dec._≟_
    }
    where module Dec = IsDecEquivalence eq

module _ {a ℓ} {A : Set a} {∼ : RawRel A ℓ} where

  isPreorder : IsPreorder ∼ → IsPreorder (flip ∼)
  isPreorder O = record
    { reflexive  = reflexive ∼ O.reflexive
    ; transitive = transitive ∼ O.transitive
    }
    where module O = IsPreorder O

  isPartialOrder : IsPartialOrder ∼ → IsPartialOrder (flip ∼)
  isPartialOrder O = record
    { isPreorder = isPreorder O.isPreorder
    ; antisym    = antisym ∼ O.antisym
    }
    where module O = IsPartialOrder O

  isTotalOrder : IsTotalOrder ∼ → IsTotalOrder (flip ∼)
  isTotalOrder O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    ; total          = totalₚ ∼ O.total
    }
    where module O = IsTotalOrder O

  isDecTotalOrder : IsDecTotalOrder ∼ → IsDecTotalOrder (flip ∼)
  isDecTotalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    ; _≤?_         = dec ∼ O._≤?_
    }
    where module O = IsDecTotalOrder O

  isStrictPartialOrder : IsStrictPartialOrder ∼ →
                         IsStrictPartialOrder (flip ∼)
  isStrictPartialOrder O = record
    { irrefl     = irrefl ∼ O.irrefl
    ; transitive = transitive ∼ O.transitive
    }
    where module O = IsStrictPartialOrder O

  isStrictTotalOrder : IsStrictTotalOrder ∼ →
                       IsStrictTotalOrder (flip ∼)
  isStrictTotalOrder O = record
    { transitive = transitive ∼ O.transitive
    ; compare    = compare ∼ O.compare
    }
    where module O = IsStrictTotalOrder O

module _ {a ℓ} {A : Type a} where

  equivalence : Equivalence A ℓ → Equivalence A ℓ
  equivalence S = record
    { isEquivalence = isEquivalence S.isEquivalence
    }
    where module S = Equivalence S

  decEquivalence : DecEquivalence A ℓ → DecEquivalence A ℓ
  decEquivalence S = record
    { isDecEquivalence = isDecEquivalence S.isDecEquivalence
    }
    where module S = DecEquivalence S

module _ {a ℓ} {A : Type a} where

  preorder : Preorder A ℓ → Preorder A ℓ
  preorder O = record
    { isPreorder = isPreorder O.isPreorder
    }
    where module O = Preorder O

  partialOrder : PartialOrder A ℓ → PartialOrder A ℓ
  partialOrder O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    }
    where module O = PartialOrder O

  totalOrder : TotalOrder A ℓ → TotalOrder A ℓ
  totalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    }
    where module O = TotalOrder O

  decTotalOrder : DecTotalOrder A ℓ → DecTotalOrder A ℓ
  decTotalOrder O = record
    { isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
    }
    where module O = DecTotalOrder O

  strictPartialOrder : StrictPartialOrder A ℓ →
                       StrictPartialOrder A ℓ
  strictPartialOrder O = record
    { isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
    }
    where module O = StrictPartialOrder O

  strictTotalOrder : StrictTotalOrder A ℓ →
                     StrictTotalOrder A ℓ
  strictTotalOrder O = record
    { isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
    }
    where module O = StrictTotalOrder O
