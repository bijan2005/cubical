{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Construct.Always where

open import Cubical.Core.Everything

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Construct.Constant using (Const)
open import Cubical.Data.Unit.Polymorphic

------------------------------------------------------------------------
-- Definition

Always : ∀ {a ℓ} {A : Type a} → Rel A ℓ
Always = Const ⊤

AlwaysProp : ∀ {a ℓ} {A : Type a} → PropRel A ℓ
AlwaysProp = Always , λ _ _ → isProp⊤

------------------------------------------------------------------------
-- Properties

module _ {a} (A : Type a) ℓ where

  reflexive : Reflexive {A = A} {ℓ = ℓ} Always
  reflexive = _

  symmetric : Symmetric {A = A} {ℓ = ℓ} Always
  symmetric _ = _

  transitive : Transitive {A = A} {ℓ = ℓ} Always
  transitive _ _ = _

  isEquivalence : IsEquivalence {ℓ = ℓ} {A} Always
  isEquivalence = record {}

  equivalence : Equivalence a ℓ
  equivalence = record
    { isEquivalence = isEquivalence
    }
