{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra
open import Cubical.Relation.Unary

module Cubical.Algebra.Semigroup.Construct.Subsemigroup {c ℓ} (S : Semigroup c) (P : PropPred ⟨ S ⟩ ℓ)
                                                            (closed : Semigroup._•_ S Preserves₂ ⟨ P ⟩ᴾ) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Semigroup.Morphism

open Semigroup S

import Cubical.Algebra.Magma.Construct.Submagma magma P closed as Submagma
open Submagma public hiding (ΣP-isMagma; ΣP-Magma; inclusion-isHom; inclusion)

------------------------------------------------------------------------
-- Properties of the subsemigroup

•ᴾ-assoc : Associative _•ᴾ_
•ᴾ-assoc _ _ _ = ΣPathTransport→PathΣ _ _ (assoc _ _ _ , P .snd _ _ _)


------------------------------------------------------------------------
-- The subsemigroup

ΣP-isSemigroup : IsSemigroup ΣP _•ᴾ_
ΣP-isSemigroup = record
  { isMagma = Submagma.ΣP-isMagma
  ; assoc   = •ᴾ-assoc
  }

ΣP-Semigroup : Semigroup (ℓ-max c ℓ)
ΣP-Semigroup = record { isSemigroup = ΣP-isSemigroup }

------------------------------------------------------------------------
-- Inclusion homomorphism

inclusion-isHom : IsSemigroupHom ΣP-Semigroup S fst
inclusion-isHom (_ , _) (_ , _) = refl

inclusion : SemigroupHom ΣP-Semigroup S
inclusion = record { isHom = inclusion-isHom }
