{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Algebra.Group

module Cubical.Algebra.Group.Construct.Opposite {ℓ} (G : Group ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod using (_,_)

open Group G

import Cubical.Algebra.Monoid.Construct.Opposite monoid as OpMonoid
open OpMonoid public hiding (Op-isMonoid; Mᵒᵖ)

•ᵒᵖ-inverseˡ : LeftInverse ε _⁻¹ _•ᵒᵖ_
•ᵒᵖ-inverseˡ _ = inverseʳ _

•ᵒᵖ-inverseʳ : RightInverse ε _⁻¹ _•ᵒᵖ_
•ᵒᵖ-inverseʳ _ = inverseˡ _

•ᵒᵖ-inverse : Inverse ε _⁻¹ _•ᵒᵖ_
•ᵒᵖ-inverse = •ᵒᵖ-inverseˡ , •ᵒᵖ-inverseʳ


Op-isGroup : IsGroup Carrier _•ᵒᵖ_ ε _⁻¹
Op-isGroup = record
  { isMonoid = OpMonoid.Op-isMonoid
  ; inverse  = •ᵒᵖ-inverse
  }

Gᵒᵖ : Group ℓ
Gᵒᵖ = record { isGroup = Op-isGroup }
