{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Construct.Empty where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Magma

open import Cubical.Data.Empty

_◯_ : Op₂ ⊥
_◯_ ()

isSet⊥ : isSet ⊥
isSet⊥ = isProp→isSet isProp⊥


⊥-isMagma : IsMagma ⊥ _◯_
⊥-isMagma = record { is-set = isSet⊥ }

⊥-Magma : Magma ℓ-zero
⊥-Magma = record { isMagma = ⊥-isMagma }
