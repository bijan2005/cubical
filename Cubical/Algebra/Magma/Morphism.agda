{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Magma.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Algebra

private
  variable
    m n : Level

IsMagmaHom : (M : Magma m) (N : Magma n) → (⟨ M ⟩ → ⟨ N ⟩) → Type (ℓ-max m n)
IsMagmaHom M N fun = Homomorphic₂ fun (Magma._•_ M) (Magma._•_ N)

record MagmaHom (M : Magma m) (N : Magma n) : Type (ℓ-max m n) where
  constructor magmahom
  field
    fun : ⟨ M ⟩ → ⟨ N ⟩
    isHom : IsMagmaHom M N fun

record MagmaEquiv (M : Magma m) (N : Magma n) : Type (ℓ-max m n) where
  constructor magmaequiv
  field
    eq : ⟨ M ⟩ ≃ ⟨ N ⟩
    isHom : IsMagmaHom M N (equivFun eq)

  hom : MagmaHom M N
  hom = record { isHom = isHom }
