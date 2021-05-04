{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Int.Base where

open import Cubical.Core.Everything

open import Cubical.Data.Nat

data ℤ : Type₀ where
  pos    : (n : ℕ) → ℤ
  negsuc : (n : ℕ) → ℤ

neg : (n : ℕ) → ℤ
neg zero = pos zero
neg (suc n) = negsuc n

infix 100 -_
-_ : ℕ → ℤ
-_ = neg

{-# DISPLAY pos n = n #-}
{-# DISPLAY negsuc n = - (suc n) #-}

sucInt : ℤ → ℤ
sucInt (pos n)          = pos (suc n)
sucInt (negsuc zero)    = pos zero
sucInt (negsuc (suc n)) = negsuc n

predInt : ℤ → ℤ
predInt (pos zero)    = negsuc zero
predInt (pos (suc n)) = pos n
predInt (negsuc n)    = negsuc (suc n)

-- Natural number and negative integer literals for ℤ

open import Cubical.Data.Nat.Literals public

instance
  fromNatℤ : FromNat ℤ
  fromNatℤ = record { Constraint = λ _ → ⊤ ; fromNat = λ n → pos n }

instance
  negativeℤ : Negative ℤ
  negativeℤ = record { Constraint = λ _ → ⊤ ; fromNeg = λ n → neg n }
