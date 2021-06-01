{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Raw.Construct.Always where

open import Cubical.Core.Everything

open import Cubical.Relation.Binary.Raw
open import Cubical.Relation.Binary.Raw.Construct.Constant using (Const)
open import Cubical.Data.Unit.Polymorphic

------------------------------------------------------------------------
-- Definition

Always : ∀ {a b ℓ} {A : Type a} {B : Type b} → RawREL A B ℓ
Always = Const ⊤

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

  equivalence : Equivalence A ℓ
  equivalence = record
    { isEquivalence = isEquivalence
    }
