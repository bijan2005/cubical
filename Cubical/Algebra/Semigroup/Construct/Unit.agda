{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Construct.Unit where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Unit

import Cubical.Algebra.Magma.Construct.Unit as ⊤Magma
open ⊤Magma public hiding (⊤-isMagma; ⊤-Magma)

◯-assoc : Associative _◯_
◯-assoc _ _ _ = refl


⊤-isSemigroup : IsSemigroup ⊤ _◯_
⊤-isSemigroup = record
  { isMagma = ⊤Magma.⊤-isMagma
  ; assoc   = ◯-assoc
  }

⊤-Semigroup : Semigroup ℓ-zero
⊤-Semigroup = record { isSemigroup = ⊤-isSemigroup }
