{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Subgroup where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Algebra
open import Cubical.Algebra.Group.Morphism
open import Cubical.Algebra.Monoid.Submonoid

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Subtype


record Subgroup {c} (G : Group c) ℓ : Type (ℓ-max c (ℓ-suc ℓ)) where
  constructor mksubgroup

  private module G = Group G

  field
    Member : Pred ⟨ G ⟩ ℓ
    preservesOp : G._•_ Preserves₂ Member
    preservesInv : G._⁻¹ Preserves Member
    preservesId : G.ε ∈ Member

  submonoid : Submonoid G.monoid ℓ
  submonoid = record
    { Member = Member
    ; preservesOp = preservesOp
    ; preservesId = preservesId
    }

  open Submonoid submonoid hiding (Member; preservesOp; preservesId; _^_) public


  _⁻¹ : Op₁ Carrier
  (x , subx) ⁻¹ = x G.⁻¹ , preservesInv subx

  inverseˡ : LeftInverse ε _⁻¹ _•_
  inverseˡ _ = ΣPathTransport→PathΣ _ _ (G.inverseˡ _ , isProp[ Member ] _ _ _)

  inverseʳ : RightInverse ε _⁻¹ _•_
  inverseʳ _ = ΣPathTransport→PathΣ _ _ (G.inverseʳ _ , isProp[ Member ] _ _ _)

  inverse : Inverse ε _⁻¹ _•_
  inverse = inverseˡ , inverseʳ


  isGroup : IsGroup Carrier _•_ ε _⁻¹
  isGroup = record
    { isMonoid = isMonoid
    ; inverse = inverse
    }

  group : Group _
  group = record { isGroup = isGroup }

  open Group group using
    ( _^_
    ; _/_
    ; _/ˡ_
    ; inv-uniqueˡ
    ; inv-uniqueʳ
    ; cancelˡ
    ; cancelʳ
    ) public


instance
  SubgroupCarrier : ∀ {c ℓ} {G : Group c} → HasCarrier (Subgroup G ℓ) _
  SubgroupCarrier = record { ⟨_⟩ = Subgroup.Carrier }
