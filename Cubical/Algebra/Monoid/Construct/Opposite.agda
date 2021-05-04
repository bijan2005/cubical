{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Algebra.Monoid

module Cubical.Algebra.Monoid.Construct.Opposite {ℓ} (M : Monoid ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Prod using (_,_)

open Monoid M

import Cubical.Algebra.Semigroup.Construct.Opposite semigroup as OpSemigroup
open OpSemigroup public hiding (Op-isSemigroup; Sᵒᵖ)

•ᵒᵖ-identityˡ : LeftIdentity ε _•ᵒᵖ_
•ᵒᵖ-identityˡ _ = identityʳ _

•ᵒᵖ-identityʳ : RightIdentity ε _•ᵒᵖ_
•ᵒᵖ-identityʳ _ = identityˡ _

•ᵒᵖ-identity : Identity ε _•ᵒᵖ_
•ᵒᵖ-identity = •ᵒᵖ-identityˡ , •ᵒᵖ-identityʳ


Op-isMonoid : IsMonoid Carrier _•ᵒᵖ_ ε
Op-isMonoid = record
  { isSemigroup = OpSemigroup.Op-isSemigroup
  ; identity    = •ᵒᵖ-identity
  }

Mᵒᵖ : Monoid ℓ
Mᵒᵖ = record { isMonoid = Op-isMonoid }
