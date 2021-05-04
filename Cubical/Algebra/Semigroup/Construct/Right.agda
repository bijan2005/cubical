{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Semigroup.Construct.Right {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Semigroup

import Cubical.Algebra.Magma.Construct.Right Aˢ as RMagma
open RMagma public hiding (Right-isMagma; RightMagma)

private
  A = ⟨ Aˢ ⟩
  isSetA = Aˢ .snd

▸-assoc : Associative _▸_
▸-assoc _ _ _ = refl


Right-isSemigroup : IsSemigroup A _▸_
Right-isSemigroup = record
  { isMagma = RMagma.Right-isMagma
  ; assoc   = ▸-assoc
  }

RightSemigroup : Semigroup ℓ
RightSemigroup = record { isSemigroup = Right-isSemigroup }
