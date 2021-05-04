{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Semigroup.Construct.Left {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Semigroup

import Cubical.Algebra.Magma.Construct.Left Aˢ as LMagma
open LMagma public hiding (Left-isMagma; LeftMagma)

private
  A = ⟨ Aˢ ⟩
  isSetA = Aˢ .snd

◂-assoc : Associative _◂_
◂-assoc _ _ _ = refl


Left-isSemigroup : IsSemigroup A _◂_
Left-isSemigroup = record
  { isMagma = LMagma.Left-isMagma
  ; assoc   = ◂-assoc
  }

LeftSemigroup : Semigroup ℓ
LeftSemigroup = record { isSemigroup = Left-isSemigroup }
