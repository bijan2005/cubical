{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra
open import Cubical.Relation.Unary

module Cubical.Algebra.Magma.Construct.Submagma {c ℓ} (M : Magma c) (P : PropPred ⟨ M ⟩ ℓ)
                                                    (closed : Magma._•_ M Preserves₂ ⟨ P ⟩ᴾ) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Magma.Morphism

open Magma M

------------------------------------------------------------------------
-- Elements of the submagma

ΣP = Σ Carrier ⟨ P ⟩ᴾ

_•ᴾ_ : Op₂ ΣP
(x , Px) •ᴾ (y , Py) = x • y , closed Px Py


------------------------------------------------------------------------
-- Properties of the submagma

isSetΣP : isSet ΣP
isSetΣP = isSetΣ is-set λ _ → isProp→isSet (P .snd _)


------------------------------------------------------------------------
-- The submagma

ΣP-isMagma : IsMagma ΣP _•ᴾ_
ΣP-isMagma = record { is-set = isSetΣP }

ΣP-Magma : Magma (ℓ-max c ℓ)
ΣP-Magma = record { isMagma = ΣP-isMagma }


------------------------------------------------------------------------
-- Inclusion homomorphism

inclusion-isHom : IsMagmaHom ΣP-Magma M fst
inclusion-isHom (_ , _) (_ , _) = refl

inclusion : MagmaHom ΣP-Magma M
inclusion = record { isHom = inclusion-isHom }
