{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary
open import Cubical.Algebra.Monoid

module Cubical.Algebra.Monoid.Construct.Quotient {c ℓ} (M : Monoid c) {R : Rel (Monoid.Carrier M) ℓ} (isEq : IsEquivalence R)
                                                              (closed : Congruent₂ R (Monoid._•_ M)) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Properties
open import Cubical.HITs.SetQuotients
open import Cubical.Data.Prod using (_,_)

open Monoid M
open IsEquivalence isEq

import Cubical.Algebra.Semigroup.Construct.Quotient semigroup isEq closed as QSemigroup
open QSemigroup public hiding (S/R-isSemigroup; S/R)

εᴿ : Carrier/R
εᴿ = [ ε ]

•ᴿ-identityˡ : LeftIdentity εᴿ _•ᴿ_
•ᴿ-identityˡ = elimProp (λ _ → squash/ _ _) (λ x → cong [_] (identityˡ x))

•ᴿ-identityʳ : RightIdentity εᴿ _•ᴿ_
•ᴿ-identityʳ = elimProp (λ _ → squash/ _ _) (λ x → cong [_] (identityʳ x))

•ᴿ-identity : Identity εᴿ _•ᴿ_
•ᴿ-identity = •ᴿ-identityˡ , •ᴿ-identityʳ


M/R-isMonoid : IsMonoid Carrier/R _•ᴿ_ εᴿ
M/R-isMonoid = record
  { isSemigroup = QSemigroup.S/R-isSemigroup
  ; identity    = •ᴿ-identity
  }

M/R : Monoid (ℓ-max c ℓ)
M/R = record { isMonoid = M/R-isMonoid }
