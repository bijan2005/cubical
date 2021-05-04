{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Bundles where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (isSet)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Definitions
open import Cubical.Relation.Binary.Structures

open import Cubical.Structures.Carrier

------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record Preorder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _∼_
  field
    Carrier    : Type c
    _∼_        : Rel Carrier ℓ  -- The relation.
    isPreorder : IsPreorder _∼_

  open IsPreorder isPreorder public

instance
  PreorderCarrier : ∀ {c ℓ} → HasCarrier (Preorder c ℓ) c
  PreorderCarrier = record { ⟨_⟩ = Preorder.Carrier }


------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

record PartialEquivalence c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  field
    Carrier              : Type c
    _≈_                  : Rel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  open IsPartialEquivalence isPartialEquivalence public

  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

instance
  PartialEquivalenceCarrier : ∀ {c ℓ} → HasCarrier (PartialEquivalence c ℓ) c
  PartialEquivalenceCarrier = record { ⟨_⟩ = PartialEquivalence.Carrier }


record Equivalence c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Type c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  partialEquivalence : PartialEquivalence c ℓ
  partialEquivalence = record
    { isPartialEquivalence = isPartialEquivalence
    }

  open PartialEquivalence partialEquivalence public using (_≉_)

  preorder : Preorder c ℓ
  preorder = record
    { isPreorder = isPreorder
    }

instance
  EquivalenceCarrier : ∀ {c ℓ} → HasCarrier (Equivalence c ℓ) c
  EquivalenceCarrier = record { ⟨_⟩ = Equivalence.Carrier }


record DecEquivalence c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≈_
  field
    Carrier          : Type c
    _≈_              : Rel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  equivalence : Equivalence c ℓ
  equivalence = record
    { isEquivalence = isEquivalence
    }

  open Equivalence equivalence public using (partialEquivalence; _≉_)

instance
  DecEquivalenceCarrier : ∀ {c ℓ} → HasCarrier (DecEquivalence c ℓ) c
  DecEquivalenceCarrier = record { ⟨_⟩ = DecEquivalence.Carrier }


------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record PartialOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≤_
  field
    Carrier        : Type c
    _≤_            : Rel Carrier ℓ
    isPartialOrder : IsPartialOrder _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder c ℓ
  preorder = record
    { isPreorder = isPreorder
    }

instance
  PartialOrderCarrier : ∀ {c ℓ} → HasCarrier (PartialOrder c ℓ) c
  PartialOrderCarrier = record { ⟨_⟩ = PartialOrder.Carrier }


record DecPartialOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≤_
  field
    Carrier           : Type c
    _≤_               : Rel Carrier ℓ
    isDecPartialOrder : IsDecPartialOrder _≤_

  open IsDecPartialOrder isDecPartialOrder public

  partialOrder : PartialOrder c ℓ
  partialOrder = record
    { isPartialOrder = isPartialOrder
    }

  open PartialOrder partialOrder public using (preorder)

instance
  DecPartialOrderCarrier : ∀ {c ℓ} → HasCarrier (DecPartialOrder c ℓ) c
  DecPartialOrderCarrier = record { ⟨_⟩ = DecPartialOrder.Carrier }


record StrictPartialOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _<_
  field
    Carrier              : Type c
    _<_                  : Rel Carrier ℓ
    isStrictPartialOrder : IsStrictPartialOrder _<_

  open IsStrictPartialOrder isStrictPartialOrder public

instance
  StrictPartialOrderCarrier : ∀ {c ℓ} → HasCarrier (StrictPartialOrder c ℓ) c
  StrictPartialOrderCarrier = record { ⟨_⟩ = StrictPartialOrder.Carrier }


record DecStrictPartialOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _<_
  field
    Carrier                 : Type c
    _<_                     : Rel Carrier ℓ
    isDecStrictPartialOrder : IsDecStrictPartialOrder _<_

  open IsDecStrictPartialOrder isDecStrictPartialOrder public

  strictPartialOrder : StrictPartialOrder c ℓ
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

instance
  DecStrictPartialOrderCarrier : ∀ {c ℓ} → HasCarrier (DecStrictPartialOrder c ℓ) c
  DecStrictPartialOrderCarrier = record { ⟨_⟩ = DecStrictPartialOrder.Carrier }


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record TotalOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≤_
  field
    Carrier      : Type c
    _≤_          : Rel Carrier ℓ
    isTotalOrder : IsTotalOrder _≤_

  open IsTotalOrder isTotalOrder public

  partialOrder : PartialOrder c ℓ
  partialOrder = record
    { isPartialOrder = isPartialOrder
    }

  open PartialOrder partialOrder public using (preorder)

instance
  TotalOrderCarrier : ∀ {c ℓ} → HasCarrier (TotalOrder c ℓ) c
  TotalOrderCarrier = record { ⟨_⟩ = TotalOrder.Carrier }


record DecTotalOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _≤_
  field
    Carrier         : Type c
    _≤_             : Rel Carrier ℓ
    isDecTotalOrder : IsDecTotalOrder _≤_

  open IsDecTotalOrder isDecTotalOrder public

  totalOrder : TotalOrder c ℓ
  totalOrder = record
    { isTotalOrder = isTotalOrder
    }

  open TotalOrder totalOrder public using (partialOrder; preorder)

  decPartialOrder : DecPartialOrder c ℓ
  decPartialOrder = record
    { isDecPartialOrder = isDecPartialOrder
    }

instance
  DecTotalOrderCarrier : ∀ {c ℓ} → HasCarrier (DecTotalOrder c ℓ) c
  DecTotalOrderCarrier = record { ⟨_⟩ = DecTotalOrder.Carrier }


-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record StrictTotalOrder c ℓ : Type (ℓ-suc (ℓ-max c ℓ)) where
  infix 4 _<_
  field
    Carrier            : Type c
    _<_                : Rel Carrier ℓ
    isStrictTotalOrder : IsStrictTotalOrder _<_

  open IsStrictTotalOrder isStrictTotalOrder public

  strictPartialOrder : StrictPartialOrder c ℓ
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

instance
  StrictTotalOrderCarrier : ∀ {c ℓ} → HasCarrier (StrictTotalOrder c ℓ) c
  StrictTotalOrderCarrier = record { ⟨_⟩ = StrictTotalOrder.Carrier }
