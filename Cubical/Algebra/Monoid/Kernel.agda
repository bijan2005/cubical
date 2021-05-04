{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra.Monoid

module Cubical.Algebra.Monoid.Kernel {ℓ₁ ℓ₂} {M : Monoid ℓ₁} {N : Monoid ℓ₂} (hom : MonoidHom M N) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Relation.Binary

module M = Monoid M
module N = Monoid N

open MonoidHom hom renaming (fun to f)

Kernel : Rel ⟨ M ⟩ ℓ₂
Kernel x y = f x ≡ f y

isPropKernel : isPropValued Kernel
isPropKernel x y = N.is-set (f x) (f y)

Kernelᴾ : PropRel ⟨ M ⟩ ℓ₂
Kernelᴾ = Kernel , isPropKernel


------------------------------------------------------------------------
-- Properties of the kernel

ker-reflexive : Reflexive Kernel
ker-reflexive = refl

ker-fromEq : FromEq Kernel
ker-fromEq = cong f

ker-symmetric : Symmetric Kernel
ker-symmetric = sym

ker-transitive : Transitive Kernel
ker-transitive = _∙_


------------------------------------------------------------------------
-- Kernel Algebra

ker-isPreorder : IsPreorder Kernel
ker-isPreorder = record
  { reflexive  = ker-reflexive
  ; transitive = ker-transitive
  }

ker-isPartialEquivalence : IsPartialEquivalence Kernel
ker-isPartialEquivalence = record
  { symmetric  = ker-symmetric
  ; transitive = ker-transitive
  }

ker-isEquivalence : IsEquivalence Kernel
ker-isEquivalence = record
  { isPartialEquivalence = ker-isPartialEquivalence
  ; reflexive            = ker-reflexive
  }


------------------------------------------------------------------------
-- Injectivity of f

ker⇒id→emb : Kernel ⇒ _≡_ → isEmbedding f
ker⇒id→emb ker⇒id = injEmbedding M.is-set N.is-set ker⇒id

emb→ker⇒id : isEmbedding f → Kernel ⇒ _≡_
emb→ker⇒id isemb {x} {y} = invIsEq (isemb x y)
