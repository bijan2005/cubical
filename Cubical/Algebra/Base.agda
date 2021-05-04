{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Base where

open import Cubical.Core.Everything

------------------------------------------------------------------------
-- Unary and binary operations

Op₁ : ∀ {ℓ} → Type ℓ → Type ℓ
Op₁ A = A → A

Op₂ : ∀ {ℓ} → Type ℓ → Type ℓ
Op₂ A = A → A → A

------------------------------------------------------------------------
-- Left and right actions

Opₗ : ∀ {a b} → Type a → Type b → Type _
Opₗ A B = A → B → B

Opᵣ : ∀ {a b} → Type a → Type b → Type _
Opᵣ A B = B → A → B
