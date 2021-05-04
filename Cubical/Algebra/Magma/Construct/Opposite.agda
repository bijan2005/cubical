{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Algebra.Magma

module Cubical.Algebra.Magma.Construct.Opposite {ℓ} (M : Magma ℓ) where

open import Cubical.Foundations.Prelude

open Magma M

_•ᵒᵖ_ : Op₂ Carrier
y •ᵒᵖ x = x • y


Op-isMagma : IsMagma Carrier _•ᵒᵖ_
Op-isMagma = record { is-set = is-set }

Mᵒᵖ : Magma ℓ
Mᵒᵖ = record { isMagma = Op-isMagma }
