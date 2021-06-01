{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Relation.Binary.Base
open import Cubical.Core.Everything

module Cubical.Relation.Binary.Structures
  {a ℓ} {A : Type a} -- The underlying type
  (_<>_ : Rel A ℓ)   -- The relation
  where

open import Cubical.Foundations.Prelude using (refl; sym; isSet)
open import Cubical.Foundations.Function using (_∘_; id)
open import Cubical.Foundations.Logic hiding (¬_)

open import Cubical.Relation.Nullary.Decidable
open import Cubical.Relation.Binary.Definitions
open import Cubical.Relation.Binary.Properties

open import Cubical.HITs.PropositionalTruncation

import Cubical.Relation.Binary.Raw.Structures [ _<>_ ] as Raw

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


  raw : Raw.IsPreorder
  raw = record
    { reflexive = reflexive
    ; transitive = transitive
    }

------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------

record IsPartialEquivalence : Type (ℓ-max a ℓ) where
  constructor ispartialeq
  field
    symmetric  : Symmetric _<>_
    transitive : Transitive _<>_


  raw : Raw.IsPartialEquivalence
  raw = record
    { symmetric = symmetric
    ; transitive = transitive
    }


record IsEquivalence : Type (ℓ-max a ℓ) where
  constructor isequivalence
  field
    reflexive            : Reflexive _<>_
    isPartialEquivalence : IsPartialEquivalence

  open IsPartialEquivalence isPartialEquivalence public hiding (raw)

  from-≡ : FromEq _<>_
  from-≡ = reflx→fromeq _<>_ reflexive

  isPreorder : IsPreorder
  isPreorder = record
    { reflexive  = reflexive
    ; transitive = transitive
    }


  raw : Raw.IsEquivalence
  raw = record
    { reflexive = reflexive
    ; isPartialEquivalence = IsPartialEquivalence.raw isPartialEquivalence
    }


record IsDecEquivalence : Type (ℓ-max a ℓ) where
  constructor isdeceq
  infix 4 _≟_
  field
    isEquivalence : IsEquivalence
    _≟_           : Decidable _<>_

  open IsEquivalence isEquivalence public hiding (raw)


  raw : Raw.IsDecEquivalence
  raw = record
    { isEquivalence = IsEquivalence.raw isEquivalence
    ; _≟_ = _≟_
    }

------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record IsPartialOrder : Type (ℓ-max a ℓ) where
  constructor ispartialorder
  field
    isPreorder : IsPreorder
    antisym    : Antisymmetric _<>_

  open IsPreorder isPreorder public hiding (raw)


  raw : isSet A → Raw.IsPartialOrder
  raw isSetA = record
    { isPreorder = IsPreorder.raw isPreorder
    ; antisym = λ x y → rec (isSetA _ _) id (antisym x y)
    }


record IsDecPartialOrder : Type (ℓ-max a ℓ) where
  constructor isdecpartialorder
  infix 4 _≤?_
  field
    isPartialOrder : IsPartialOrder
    _≤?_           : Decidable _<>_

  open IsPartialOrder isPartialOrder public hiding (raw)

  private
    lemma : ∀ {x y} → ¬ ⟨ x <> y ⟩ → ¬ x ≡ y
    lemma x≰y x≡y = x≰y (fromEq ∣ x≡y ∣)


  raw : isSet A → Raw.IsDecPartialOrder
  raw isSetA = record
    { isPartialOrder = IsPartialOrder.raw isPartialOrder isSetA
    ; _≤?_ = _≤?_
    }


record IsStrictPartialOrder : Type (ℓ-max a ℓ) where
  constructor isstrictpartialorder
  field
    irrefl     : Irreflexive _<>_
    transitive : Transitive _<>_

  asym : Asymmetric _<>_
  asym {x} {y} = trans∧irr→asym _<>_ transitive irrefl


  raw : Raw.IsStrictPartialOrder
  raw = record
    { irrefl = irrefl
    ; transitive = transitive
    }


record IsDecStrictPartialOrder : Type (ℓ-max a ℓ) where
  constructor isdecstrictpartialorder
  infix 4 _<?_
  field
    isStrictPartialOrder : IsStrictPartialOrder
    _<?_                 : Decidable _<>_

  open IsStrictPartialOrder isStrictPartialOrder public hiding (raw)


  raw : isSet A → Raw.IsDecStrictPartialOrder
  raw isSetA = record
    { isStrictPartialOrder = IsStrictPartialOrder.raw isStrictPartialOrder
    ; _<?_ = _<?_
    }


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record IsTotalOrder : Type (ℓ-max a ℓ) where
  constructor istotalorder
  field
    isPartialOrder : IsPartialOrder
    total          : Total _<>_

  open IsPartialOrder isPartialOrder public hiding (raw)


  raw : isSet A → Raw.IsTotalOrder
  raw isSetA = record
    { isPartialOrder = IsPartialOrder.raw isPartialOrder isSetA
    ; total = total
    }


record IsDecTotalOrder : Type (ℓ-max a ℓ) where
  constructor isdectotalorder
  infix 4 _≤?_
  field
    isTotalOrder : IsTotalOrder
    _≤?_         : Decidable _<>_

  open IsTotalOrder isTotalOrder public hiding (raw)

  isDecPartialOrder : IsDecPartialOrder
  isDecPartialOrder = record
    { isPartialOrder = isPartialOrder
    ; _≤?_           = _≤?_
    }


  raw : isSet A → Raw.IsDecTotalOrder
  raw isSetA = record
    { isTotalOrder = IsTotalOrder.raw isTotalOrder isSetA
    ; _≤?_ = _≤?_
    }


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

  open IsStrictPartialOrder isStrictPartialOrder public hiding (transitive; raw)


  raw : isSet A → Raw.IsStrictTotalOrder
  raw isSetA = record
    { transitive = transitive
    ; compare = triRaw compare
    }
    where
      import Cubical.Relation.Binary.Raw.Definitions as RawDefinitions
      triRaw : Trichotomous _<>_ → RawDefinitions.Trichotomous [ _<>_ ]
      triRaw tri x y with tri x y
      ... | tri< a b c = RawDefinitions.tri< a b c
      ... | tri≡ a b c = RawDefinitions.tri≡ a b c
      ... | tri> a b c = RawDefinitions.tri> a b c
