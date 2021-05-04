{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Structures.Carrier where

open import Cubical.Core.Everything

record HasCarrier {a} (A : Type a) ℓ : Type (ℓ-max a (ℓ-suc ℓ)) where
  field
    ⟨_⟩ : A → Type ℓ

open HasCarrier {{...}} public

instance
  -- Used for any case where sigma types are used to encode types with structure
  ΣCarrier : ∀ {ℓ ℓ′} {P : Type ℓ → Type ℓ′} → HasCarrier (Σ (Type ℓ) P) ℓ
  ΣCarrier = record { ⟨_⟩ = fst }
