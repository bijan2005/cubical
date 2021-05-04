{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary
open import Cubical.Algebra.Magma

module Cubical.Algebra.Magma.Construct.Quotient {c ℓ} (M : Magma c) {R : Rel ⟨ M ⟩ ℓ} (isEq : IsEquivalence R)
                                                    (closed : Congruent₂ R (Magma._•_ M)) where

open import Cubical.Algebra.Properties
open import Cubical.HITs.SetQuotients

open Magma M
open IsEquivalence isEq

Carrier/R = Carrier / R

_•ᴿ_ : Op₂ Carrier/R
_•ᴿ_ = rec2 squash/ (λ x y → [ x • y ]) (λ _ _ _ eq → eq/ _ _ (cong₂⇒rcong R reflexive _•_ closed eq))
                                        (λ _ _ _ eq → eq/ _ _ (cong₂⇒lcong R reflexive _•_ closed eq))

M/R-isMagma : IsMagma Carrier/R _•ᴿ_
M/R-isMagma = record { is-set = squash/ }

M/R : Magma (ℓ-max c ℓ)
M/R = record { isMagma = M/R-isMagma }
