{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Subsemigroup where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Semigroup.Morphism
open import Cubical.Algebra.Magma.Submagma

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record Subsemigroup {c} (S : Semigroup c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubsemigroup

  private module S = Semigroup S

  field
    Member : Pred ⟨ S ⟩ ℓ
    closed : S._•_ Preserves₂ Member

  submagma : Submagma S.magma ℓ
  submagma = record { Member = Member; closed = closed }

  open Submagma submagma hiding (Member; closed) public


  assoc : Associative _•_
  assoc _ _ _ = ΣPathTransport→PathΣ _ _ (S.assoc _ _ _ , isProp[ Member ] _ _ _)


  isSemigroup : IsSemigroup Carrier _•_
  isSemigroup = record
    { isMagma = isMagma
    ; assoc = assoc
    }

  semigroup : Semigroup _
  semigroup = record { isSemigroup = isSemigroup }

  open Semigroup semigroup using (_^_) public


instance
  SubsemigroupCarrier : ∀ {c ℓ} {S : Semigroup c} → HasCarrier (Subsemigroup S ℓ) _
  SubsemigroupCarrier = record { ⟨_⟩ = Subsemigroup.Carrier }
