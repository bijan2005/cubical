{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding

open import Cubical.Algebra

private
  variable
    s t : Level

IsSemigroupHom : (S : Semigroup s) (T : Semigroup t) → (⟨ S ⟩ → ⟨ T ⟩) → Type (ℓ-max s t)
IsSemigroupHom S T fun = Homomorphic₂ fun (Semigroup._•_ S) (Semigroup._•_ T)

record SemigroupHom (S : Semigroup s) (T : Semigroup t) : Type (ℓ-max s t) where
  constructor semigrouphom
  field
    fun : ⟨ S ⟩ → ⟨ T ⟩
    isHom : IsSemigroupHom S T fun

record SemigroupEquiv (S : Semigroup s) (T : Semigroup t) : Type (ℓ-max s t) where
  constructor semigroupequiv
  field
    eq : ⟨ S ⟩ ≃ ⟨ T ⟩
    isHom : IsSemigroupHom S T (equivFun eq)

  hom : SemigroupHom S T
  hom = record { isHom = isHom }
