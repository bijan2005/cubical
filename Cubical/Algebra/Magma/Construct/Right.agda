{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Magma.Construct.Right {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Magma

private
  A = ⟨ Aˢ ⟩
  isSetA = Aˢ .snd

_▸_ : Op₂ A
x ▸ y = y


------------------------------------------------------------------------
-- Properties

▸-identityˡ : ∀ x → LeftIdentity x _▸_
▸-identityˡ _ _ = refl

▸-zeroʳ : ∀ x → RightZero x _▸_
▸-zeroʳ _ _ = refl


------------------------------------------------------------------------
-- Magma definition

Right-isMagma : IsMagma A _▸_
Right-isMagma = record { is-set = isSetA }

RightMagma : Magma ℓ
RightMagma = record { isMagma = Right-isMagma }
