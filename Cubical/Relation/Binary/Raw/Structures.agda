{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Relation.Binary.Base
open import Cubical.Core.Everything

module Cubical.Relation.Binary.Raw.Structures
  {a ℓ} {A : Type a} -- The underlying type
  (_<>_ : RawRel A ℓ)   -- The relation
  where

open import Cubical.Foundations.Prelude using (refl; sym)
open import Cubical.Foundations.Function using (_∘_)

open import Cubical.Data.Prod.Base using (proj₁; proj₂; _,_)
open import Cubical.Relation.Nullary.Decidable
open import Cubical.Relation.Binary.Raw.Definitions
open import Cubical.Relation.Binary.Raw.Properties

private
  variable
    ℓ₂ : Level


------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record IsPreorder : Type (ℓ-max a ℓ) where
  constructor ispreorder
  field
    reflexive  : Reflexive _<>_
    transitive : Transitive _<>_

  fromEq : FromEq _<>_
  fromEq = reflx→fromeq _<>_ reflexive


------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

record IsPartialEquivalence : Type (ℓ-max a ℓ) where
  constructor ispartialeq
  field
    symmetric  : Symmetric _<>_
    transitive : Transitive _<>_


record IsEquivalence : Type (ℓ-max a ℓ) where
  constructor isequivalence
  field
    reflexive            : Reflexive _<>_
    isPartialEquivalence : IsPartialEquivalence

  open IsPartialEquivalence isPartialEquivalence public

  from-≡ : FromEq _<>_
  from-≡ = reflx→fromeq _<>_ reflexive

  isPreorder : IsPreorder
  isPreorder = record
    { reflexive  = reflexive
    ; transitive = transitive
    }


record IsDecEquivalence : Type (ℓ-max a ℓ) where
  constructor isdeceq
  infix 4 _≟_
  field
    isEquivalence : IsEquivalence
    _≟_           : Decidable _<>_

  open IsEquivalence isEquivalence public

------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record IsPartialOrder : Type (ℓ-max a ℓ) where
  constructor ispartialorder
  field
    isPreorder : IsPreorder
    antisym    : Antisymmetric _<>_

  open IsPreorder isPreorder public


record IsDecPartialOrder : Type (ℓ-max a ℓ) where
  constructor isdecpartialorder
  infix 4 _≤?_
  field
    isPartialOrder : IsPartialOrder
    _≤?_           : Decidable _<>_

  open IsPartialOrder isPartialOrder public

  private
    lemma : ∀ {x y} → ¬ x <> y → ¬ x ≡ y
    lemma x≰y x≡y = x≰y (fromEq x≡y)

  _≟_ : Discrete A
  _≟_ x y with x ≤? y
  ... | no ¬p = no (lemma ¬p)
  ... | yes p with y ≤? x
  ...   | no ¬q = no (lemma ¬q ∘ sym)
  ...   | yes q = yes (antisym p q)

record IsStrictPartialOrder : Type (ℓ-max a ℓ) where
  constructor isstrictpartialorder
  field
    irrefl     : Irreflexive _<>_
    transitive : Transitive _<>_

  asym : Asymmetric _<>_
  asym {x} {y} = trans∧irr→asym _<>_ transitive irrefl


record IsDecStrictPartialOrder : Type (ℓ-max a ℓ) where
  constructor isdecstrictpartialorder
  infix 4 _<?_
  field
    isStrictPartialOrder : IsStrictPartialOrder
    _<?_                 : Decidable _<>_

  open IsStrictPartialOrder isStrictPartialOrder public

------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record IsTotalOrder : Type (ℓ-max a ℓ) where
  constructor istotalorder
  field
    isPartialOrder : IsPartialOrder
    total          : PropTotal _<>_

  open IsPartialOrder isPartialOrder public


record IsDecTotalOrder : Type (ℓ-max a ℓ) where
  constructor isdectotalorder
  infix 4 _≤?_
  field
    isTotalOrder : IsTotalOrder
    _≤?_         : Decidable _<>_

  open IsTotalOrder isTotalOrder public

  isDecPartialOrder : IsDecPartialOrder
  isDecPartialOrder = record
    { isPartialOrder = isPartialOrder
    ; _≤?_           = _≤?_
    }

  open IsDecPartialOrder isDecPartialOrder public using (_≟_)

-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record IsStrictTotalOrder : Type (ℓ-max a ℓ) where
  constructor isstricttotalorder
  field
    transitive : Transitive _<>_
    compare    : Trichotomous _<>_

  infix 4 _<?_

  _<?_ : Decidable _<>_
  _<?_ = tri→dec< _<>_ compare

  _≟_ : Discrete A
  _≟_ = tri→dec≡ _<>_ compare

  isStrictPartialOrder : IsStrictPartialOrder
  isStrictPartialOrder = record
    { irrefl     = tri→irr _<>_ compare
    ; transitive = transitive
    }

  isDecStrictPartialOrder : IsDecStrictPartialOrder
  isDecStrictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    ; _<?_                 = _<?_
    }

  open IsStrictPartialOrder isStrictPartialOrder public hiding (transitive)
