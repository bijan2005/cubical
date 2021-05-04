{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Algebra.Semigroup

module Cubical.Algebra.Semigroup.Construct.Opposite {ℓ} (S : Semigroup ℓ) where

open import Cubical.Foundations.Prelude

open Semigroup S

import Cubical.Algebra.Magma.Construct.Opposite magma as OpMagma
open OpMagma public hiding (Op-isMagma; Mᵒᵖ)

•ᵒᵖ-assoc : Associative _•ᵒᵖ_
•ᵒᵖ-assoc _ _ _ = sym (assoc _ _ _)


Op-isSemigroup : IsSemigroup Carrier _•ᵒᵖ_
Op-isSemigroup = record
  { isMagma = OpMagma.Op-isMagma
  ; assoc   = •ᵒᵖ-assoc
  }

Sᵒᵖ : Semigroup ℓ
Sᵒᵖ = record { isSemigroup = Op-isSemigroup }
