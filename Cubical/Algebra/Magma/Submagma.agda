{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Submagma where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra
open import Cubical.Algebra.Magma.Morphism

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record Submagma {c} (M : Magma c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubmagma

  private module M = Magma M

  field
    Member : Pred ⟨ M ⟩ ℓ
    closed : M._•_ Preserves₂ Member

  Carrier : Type _
  Carrier = Subtype Member

  _•_ : Op₂ Carrier
  (x , subx) • (y , suby) = x M.• y , closed subx suby

  is-set : isSet Carrier
  is-set = isSetSubtype Member M.is-set


  isMagma : IsMagma Carrier _•_
  isMagma = record { is-set = is-set }

  magma : Magma _
  magma = record { isMagma = isMagma }

  open Magma magma using (set) public


instance
  SubmagmaCarrier : ∀ {c ℓ} {M : Magma c} → HasCarrier (Submagma M ℓ) _
  SubmagmaCarrier = record { ⟨_⟩ = Submagma.Carrier }
