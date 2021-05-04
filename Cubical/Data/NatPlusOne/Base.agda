{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Data.NatPlusOne.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty

record ℕ₊₁ : Type₀ where
  constructor 1+_
  field
    n : ℕ

{-# DISPLAY 1+_ n = suc n #-}

pattern one = 1+ zero
pattern 2+_ n = 1+ (suc n)

-1+_ : ℕ₊₁ → ℕ
-1+ (1+ n) = n

ℕ₊₁→ℕ : ℕ₊₁ → ℕ
ℕ₊₁→ℕ (1+ n) = suc n

suc₊₁ : ℕ₊₁ → ℕ₊₁
suc₊₁ (1+ n) = 1+ (suc n)

-- Natural number literals for ℕ₊₁

open import Cubical.Data.Nat.Literals public

instance
  fromNatℕ₊₁ : FromNat ℕ₊₁
  fromNatℕ₊₁ = record { Constraint = λ { zero → ⊥ ; _ → ⊤ }
                      ; fromNat = λ { (suc n) → 1+ n } }
