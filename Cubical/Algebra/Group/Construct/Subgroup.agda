{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra
open import Cubical.Relation.Unary

module Cubical.Algebra.Group.Construct.Subgroup {c ℓ} (G : Group c) (P : PropPred ⟨ G ⟩ ℓ)
                                                    (closedOp  : Group._•_ G Preserves₂ ⟨ P ⟩ᴾ)
                                                    (closedId  : ⟨ P ⟩ᴾ (Group.ε G))
                                                    (closedInv : Group._⁻¹ G Preserves ⟨ P ⟩ᴾ) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Prod using (_,_)
open import Cubical.Algebra.Group.Morphism

open Group G

import Cubical.Algebra.Monoid.Construct.Submonoid monoid P closedOp closedId as Submonoid
open Submonoid public hiding (ΣP-isMonoid; ΣP-Monoid; inclusion-isHom; inclusion)

------------------------------------------------------------------------
-- Elements of the subgroup

_⁻¹ᴾ : Op₁ ΣP
(x , Px) ⁻¹ᴾ = x ⁻¹ , closedInv Px


------------------------------------------------------------------------
-- Properties of the subgroup

invᴾ-inverseˡ : LeftInverse εᴾ _⁻¹ᴾ _•ᴾ_
invᴾ-inverseˡ _ = ΣPathTransport→PathΣ _ _ (inverseˡ _ , P .snd _ _ _)

invᴾ-inverseʳ : RightInverse εᴾ _⁻¹ᴾ _•ᴾ_
invᴾ-inverseʳ _ = ΣPathTransport→PathΣ _ _ (inverseʳ _ , P .snd _ _ _)

invᴾ-inverse : Inverse εᴾ _⁻¹ᴾ _•ᴾ_
invᴾ-inverse = invᴾ-inverseˡ , invᴾ-inverseʳ


------------------------------------------------------------------------
-- The subgroup

ΣP-isGroup : IsGroup ΣP _•ᴾ_ εᴾ _⁻¹ᴾ
ΣP-isGroup = record
  { isMonoid = Submonoid.ΣP-isMonoid
  ; inverse  = invᴾ-inverse
  }

ΣP-Group : Group (ℓ-max c ℓ)
ΣP-Group = record { isGroup = ΣP-isGroup }


------------------------------------------------------------------------
-- Inclusion homomorphism

inclusion-isHom : IsGroupHom ΣP-Group G fst
inclusion-isHom .IsGroupHom.preservesOp (_ , _) (_ , _) = refl

inclusion : GroupHom ΣP-Group G
inclusion = record { isHom = inclusion-isHom }
