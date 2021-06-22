{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Submonoid where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Monoid.Morphism
open import Cubical.Algebra.Semigroup.Subsemigroup

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record Submonoid {c} (M : Monoid c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubmonoid

  private
    module M = Monoid M

  field
    Member : Pred ⟨ M ⟩ ℓ
    preservesOp : M._•_ Preserves₂ Member
    preservesId : M.ε ∈ Member

  subsemigroup : Subsemigroup M.semigroup ℓ
  subsemigroup = record { Member = Member; closed = preservesOp }

  open Subsemigroup subsemigroup hiding (Member; closed; _^_) public


  ε : Carrier
  ε = M.ε , preservesId

  identityˡ : LeftIdentity ε _•_
  identityˡ _ = ΣPathTransport→PathΣ _ _ (M.identityˡ _ , isProp[ Member ] _ _ _)

  identityʳ : RightIdentity ε _•_
  identityʳ _ = ΣPathTransport→PathΣ _ _ (M.identityʳ _ , isProp[ Member ] _ _ _)

  identity : Identity ε _•_
  identity = identityˡ , identityʳ


  isMonoid : IsMonoid Carrier _•_ ε
  isMonoid = record
    { isSemigroup = isSemigroup
    ; identity = identity
    }

  monoid : Monoid _
  monoid = record { isMonoid = isMonoid }

  open Monoid monoid using (ε-uniqueˡ; ε-uniqueʳ; _^_) public


instance
  SubmonoidCarrier : ∀ {c ℓ} {M : Monoid c} → HasCarrier (Submonoid M ℓ) _
  SubmonoidCarrier = record { ⟨_⟩ = Submonoid.Carrier }
