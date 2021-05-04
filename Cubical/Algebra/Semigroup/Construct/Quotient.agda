{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary
open import Cubical.Algebra.Semigroup

module Cubical.Algebra.Semigroup.Construct.Quotient {c ℓ} (S : Semigroup c) {R : Rel (Semigroup.Carrier S) ℓ} (isEq : IsEquivalence R)
                                                              (closed : Congruent₂ R (Semigroup._•_ S)) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Properties
open import Cubical.HITs.SetQuotients

open Semigroup S
open IsEquivalence isEq

import Cubical.Algebra.Magma.Construct.Quotient magma isEq closed as QMagma
open QMagma public hiding (M/R-isMagma; M/R)

•ᴿ-assoc : Associative _•ᴿ_
•ᴿ-assoc = elimProp3 (λ _ _ _ → squash/ _ _) (λ x y z → cong [_] (assoc x y z))


S/R-isSemigroup : IsSemigroup Carrier/R _•ᴿ_
S/R-isSemigroup = record
  { isMagma = QMagma.M/R-isMagma
  ; assoc   = •ᴿ-assoc
  }

S/R : Semigroup (ℓ-max c ℓ)
S/R = record { isSemigroup = S/R-isSemigroup }
