{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra
open import Cubical.Relation.Unary

module Cubical.Algebra.Monoid.Construct.Submonoid {c ℓ} (M : Monoid c) (P : PropPred ⟨ M ⟩ ℓ)
                                                      (closedOp : Monoid._•_ M Preserves₂ ⟨ P ⟩ᴾ)
                                                      (closedId : ⟨ P ⟩ᴾ (Monoid.ε M)) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Prod using (_,_)
open import Cubical.Algebra.Monoid.Morphism

open Monoid M

import Cubical.Algebra.Semigroup.Construct.Subsemigroup semigroup P closedOp as Subsemigroup
open Subsemigroup public hiding (ΣP-isSemigroup; ΣP-Semigroup; inclusion-isHom; inclusion)

------------------------------------------------------------------------
-- Elements of the submonoid

εᴾ : ΣP
εᴾ = ε , closedId


------------------------------------------------------------------------
-- Properties of the submonoid

•ᴾ-identityˡ : LeftIdentity εᴾ _•ᴾ_
•ᴾ-identityˡ _ = ΣPathTransport→PathΣ _ _ (identityˡ _ , P .snd _ _ _)

•ᴾ-identityʳ : RightIdentity εᴾ _•ᴾ_
•ᴾ-identityʳ _ = ΣPathTransport→PathΣ _ _ (identityʳ _ , P .snd _ _ _)

•ᴾ-identity : Identity εᴾ _•ᴾ_
•ᴾ-identity = •ᴾ-identityˡ , •ᴾ-identityʳ


------------------------------------------------------------------------
-- The submonoid

ΣP-isMonoid : IsMonoid ΣP _•ᴾ_ εᴾ
ΣP-isMonoid = record
  { isSemigroup = Subsemigroup.ΣP-isSemigroup
  ; identity    = •ᴾ-identity
  }

ΣP-Monoid : Monoid (ℓ-max c ℓ)
ΣP-Monoid = record { isMonoid = ΣP-isMonoid }


------------------------------------------------------------------------
-- Inclusion homomorphism

inclusion-isHom : IsMonoidHom ΣP-Monoid M fst
inclusion-isHom .IsMonoidHom.preservesOp (_ , _) (_ , _) = refl
inclusion-isHom .IsMonoidHom.preservesId = refl

inclusion : MonoidHom ΣP-Monoid M
inclusion = record { isHom = inclusion-isHom }
