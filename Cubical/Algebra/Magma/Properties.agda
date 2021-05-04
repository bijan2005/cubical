{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Algebra
open import Cubical.Algebra.Magma.Morphism

open import Cubical.Algebra.Magma.MorphismProperties public
  using (MagmaPath; uaMagma; carac-uaMagma; Magma≡; caracMagma≡)

private
  variable
    ℓ : Level

isPropIsMagma : {M : Type ℓ} {_•_ : Op₂ M} → isProp (IsMagma M _•_)
isPropIsMagma (ismagma x) (ismagma y) = cong ismagma (isPropIsSet x y)
