{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Reasoning.Equality where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    A : Type ℓ

infixr 1 _≡⟨⟩_ _≡⟨_⟩_ _≡˘⟨_⟩_
infix 2 _∎

-- Step with a non-trivial propositional equality

_≡⟨_⟩_ : ∀ x {y z : A} → x ≡ y → y ≡ z → x ≡ z
_≡⟨_⟩_ x = _∙_

-- Step with a flipped non-trivial propositional equality

_≡˘⟨_⟩_ : ∀ x {y z : A} → y ≡ x → y ≡ z → x ≡ z
x ≡˘⟨ y≡x ⟩ y≡z = x ≡⟨ sym y≡x ⟩ y≡z

-- Step with a trivial propositional equality

_≡⟨⟩_ : ∀ x {y : A} → x ≡ y → x ≡ y
_ ≡⟨⟩ x≡y = x≡y

-- Syntax for path definition

≡⟨⟩-syntax : ∀ x {y z : A} → x ≡ y → y ≡ z → x ≡ z
≡⟨⟩-syntax = _≡⟨_⟩_
infixr 1 ≡⟨⟩-syntax
syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y

≡˘⟨⟩-syntax : ∀ x {y z : A} → y ≡ x → y ≡ z → x ≡ z
≡˘⟨⟩-syntax = _≡˘⟨_⟩_
infixr 1 ≡˘⟨⟩-syntax
syntax ≡˘⟨⟩-syntax x (λ i → B) y = x ≡˘[ i ]⟨ B ⟩ y

-- Termination step

_∎ : ∀ (x : A) → x ≡ x
x ∎ = refl
