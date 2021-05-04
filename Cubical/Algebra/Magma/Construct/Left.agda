{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Magma.Construct.Left {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Magma

private
  A = ⟨ Aˢ ⟩
  isSetA = Aˢ .snd

_◂_ : Op₂ A
x ◂ y = x


------------------------------------------------------------------------
-- Properties

◂-zeroˡ : ∀ x → LeftZero x _◂_
◂-zeroˡ _ _ = refl

◂-identityʳ : ∀ x → RightIdentity x _◂_
◂-identityʳ _ _ = refl


------------------------------------------------------------------------
-- Magma definition

Left-isMagma : IsMagma A _◂_
Left-isMagma = record { is-set = isSetA }

LeftMagma : Magma ℓ
LeftMagma = record { isMagma = Left-isMagma }
