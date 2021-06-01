{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything

module Cubical.Relation.Binary.Raw.Bundles {c : Level} (Carrier : Type c) where

open import Cubical.Foundations.Prelude using (isSet)

open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Binary.Raw.Definitions
open import Cubical.Relation.Binary.Raw.Structures


------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record Preorder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _∼_
  field
    _∼_        : RawRel Carrier ℓ
    isPreorder : IsPreorder _∼_

  open IsPreorder isPreorder public


------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

record PartialEquivalence ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  field
    _≈_                  : RawRel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  open IsPartialEquivalence isPartialEquivalence public

  _≉_ : RawRel Carrier _
  x ≉ y = ¬ (x ≈ y)


record Equivalence ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≈_
  field
    _≈_           : RawRel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  partialEquivalence : PartialEquivalence ℓ
  partialEquivalence = record
    { isPartialEquivalence = isPartialEquivalence
    }

  open PartialEquivalence partialEquivalence public using (_≉_)

  preorder : Preorder ℓ
  preorder = record
    { isPreorder = isPreorder
    }


record DecEquivalence ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≈_
  field
    _≈_              : RawRel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  equivalence : Equivalence ℓ
  equivalence = record
    { isEquivalence = isEquivalence
    }

  open Equivalence equivalence public using (partialEquivalence; _≉_)


------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record PartialOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≤_
  field
    _≤_            : RawRel Carrier ℓ
    isPartialOrder : IsPartialOrder _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder ℓ
  preorder = record
    { isPreorder = isPreorder
    }


record DecPartialOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≤_
  field
    _≤_               : RawRel Carrier ℓ
    isDecPartialOrder : IsDecPartialOrder _≤_

  open IsDecPartialOrder isDecPartialOrder public

  partialOrder : PartialOrder ℓ
  partialOrder = record
    { isPartialOrder = isPartialOrder
    }

  open PartialOrder partialOrder public using (preorder)


record StrictPartialOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _<_
  field
    _<_                  : RawRel Carrier ℓ
    isStrictPartialOrder : IsStrictPartialOrder _<_

  open IsStrictPartialOrder isStrictPartialOrder public


record DecStrictPartialOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _<_
  field
    _<_                     : RawRel Carrier ℓ
    isDecStrictPartialOrder : IsDecStrictPartialOrder _<_

  open IsDecStrictPartialOrder isDecStrictPartialOrder public

  strictPartialOrder : StrictPartialOrder ℓ
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record TotalOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≤_
  field
    _≤_          : RawRel Carrier ℓ
    isTotalOrder : IsTotalOrder _≤_

  open IsTotalOrder isTotalOrder public

  partialOrder : PartialOrder ℓ
  partialOrder = record
    { isPartialOrder = isPartialOrder
    }

  open PartialOrder partialOrder public using (preorder)


record DecTotalOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _≤_
  field
    _≤_             : RawRel Carrier ℓ
    isDecTotalOrder : IsDecTotalOrder _≤_

  open IsDecTotalOrder isDecTotalOrder public

  totalOrder : TotalOrder ℓ
  totalOrder = record
    { isTotalOrder = isTotalOrder
    }

  open TotalOrder totalOrder public using (partialOrder; preorder)

  decPartialOrder : DecPartialOrder ℓ
  decPartialOrder = record
    { isDecPartialOrder = isDecPartialOrder
    }


-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record StrictTotalOrder ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  infix 4 _<_
  field
    _<_                : RawRel Carrier ℓ
    isStrictTotalOrder : IsStrictTotalOrder _<_

  open IsStrictTotalOrder isStrictTotalOrder public

  strictPartialOrder : StrictPartialOrder ℓ
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }
