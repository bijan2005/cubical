{-# OPTIONS --cubical --without-K --safe #-}

open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Construct.Converse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Prod

------------------------------------------------------------------------
-- Properties

module _ {a ℓ} {A : Set a} (∼ : Rel A ℓ) where

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

module _ {a ℓ₁ ℓ₂} {A : Set a} (∼₁ : Rel A ℓ₁) (∼₂ : Rel A ℓ₂) where

  resp₂ : ∼₁ Respects₂ ∼₂ → (flip ∼₁) Respects₂ ∼₂
  resp₂ (resp₁ , resp₂) = resp₂ , resp₁

module _ {a b ℓ} {A : Set a} {B : Set b} (∼ : REL A B ℓ) where

  dec : Decidable ∼ → Decidable (flip ∼)
  dec dec = flip dec

------------------------------------------------------------------------
-- Structures

module _ {a ℓ} {A : Set a} {≈ : Rel A ℓ} where

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

module _ {a ℓ} {A : Set a} {∼ : Rel A ℓ} where

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
    ; total          = total ∼ O.total
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

module _ {a ℓ} where

  equivalence : Equivalence a ℓ → Equivalence a ℓ
  equivalence S = record
    { isEquivalence = isEquivalence S.isEquivalence
    }
    where module S = Equivalence S

  decEquivalence : DecEquivalence a ℓ → DecEquivalence a ℓ
  decEquivalence S = record
    { isDecEquivalence = isDecEquivalence S.isDecEquivalence
    }
    where module S = DecEquivalence S

module _ {a ℓ} where

  preorder : Preorder a ℓ → Preorder a ℓ
  preorder O = record
    { isPreorder = isPreorder O.isPreorder
    }
    where module O = Preorder O

  partialOrder : PartialOrder a ℓ → PartialOrder a ℓ
  partialOrder O = record
    { isPartialOrder = isPartialOrder O.isPartialOrder
    }
    where module O = PartialOrder O

  totalOrder : TotalOrder a ℓ → TotalOrder a ℓ
  totalOrder O = record
    { isTotalOrder = isTotalOrder O.isTotalOrder
    }
    where module O = TotalOrder O

  decTotalOrder : DecTotalOrder a ℓ → DecTotalOrder a ℓ
  decTotalOrder O = record
    { isDecTotalOrder = isDecTotalOrder O.isDecTotalOrder
    }
    where module O = DecTotalOrder O

  strictPartialOrder : StrictPartialOrder a ℓ →
                       StrictPartialOrder a ℓ
  strictPartialOrder O = record
    { isStrictPartialOrder = isStrictPartialOrder O.isStrictPartialOrder
    }
    where module O = StrictPartialOrder O

  strictTotalOrder : StrictTotalOrder a ℓ →
                     StrictTotalOrder a ℓ
  strictTotalOrder O = record
    { isStrictTotalOrder = isStrictTotalOrder O.isStrictTotalOrder
    }
    where module O = StrictTotalOrder O
