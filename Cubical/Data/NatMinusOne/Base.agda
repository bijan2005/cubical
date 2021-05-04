{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Data.NatMinusOne.Base where

open import Cubical.Core.Primitives
open import Cubical.Data.Nat
open import Cubical.Data.Empty
open import Cubical.Data.Int.Base using (ℤ; pos; negsuc; -_)

record ℕ₋₁ : Type₀ where
  constructor -1+_
  field
    n : ℕ

pattern neg1 = -1+ zero
pattern ℕ→ℕ₋₁ n = -1+ (suc n)

1+_ : ℕ₋₁ → ℕ
1+_ (-1+ n) = n

suc₋₁ : ℕ₋₁ → ℕ₋₁
suc₋₁ (-1+ n) = -1+ (suc n)

-- Natural number and negative integer literals for ℕ₋₁

open import Cubical.Data.Nat.Literals public

instance
  fromNatℕ₋₁ : FromNat ℕ₋₁
  fromNatℕ₋₁ = record { Constraint = λ _ → ⊤ ; fromNat = ℕ→ℕ₋₁ }

instance
  negativeℕ₋₁ : Negative ℕ₋₁
  negativeℕ₋₁ = record { Constraint = λ { (suc (suc _)) → ⊥ ; _ → ⊤ }
                      ; fromNeg = λ { zero → 0 ; (suc zero) → neg1 } }
