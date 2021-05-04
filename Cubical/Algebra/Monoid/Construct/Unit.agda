{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Monoid.Construct.Unit where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Monoid
open import Cubical.Data.Prod using (_,_)

open import Cubical.Data.Unit

import Cubical.Algebra.Semigroup.Construct.Unit as ⊤Semigroup
open ⊤Semigroup public hiding (⊤-isSemigroup; ⊤-Semigroup)

◯-identityˡ : LeftIdentity tt _◯_
◯-identityˡ _ = refl

◯-identityʳ : RightIdentity tt _◯_
◯-identityʳ _ = refl

◯-identity : Identity tt _◯_
◯-identity = ◯-identityˡ , ◯-identityʳ


⊤-isMonoid : IsMonoid ⊤ _◯_ tt
⊤-isMonoid = record
  { isSemigroup = ⊤Semigroup.⊤-isSemigroup
  ; identity    = ◯-identity
  }

⊤-Monoid : Monoid ℓ-zero
⊤-Monoid = record { isMonoid = ⊤-isMonoid }
