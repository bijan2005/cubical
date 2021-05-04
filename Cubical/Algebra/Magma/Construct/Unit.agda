{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Construct.Unit where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Magma

open import Cubical.Data.Unit

_◯_ : Op₂ ⊤
_ ◯ _ = tt


⊤-isMagma : IsMagma ⊤ _◯_
⊤-isMagma = record { is-set = isSet⊤ }

⊤-Magma : Magma ℓ-zero
⊤-Magma = record { isMagma = ⊤-isMagma }
