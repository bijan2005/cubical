{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Semigroup.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Semigroup.Morphism
open import Cubical.Algebra.Magma.Properties using (isPropIsMagma)

open import Cubical.Relation.Binary.Reasoning.Equality

open import Cubical.Algebra.Semigroup.MorphismProperties public
  using (SemigroupPath; uaSemigroup; carac-uaSemigroup; Semigroup≡; caracSemigroup≡)

private
  variable
    ℓ : Level

isPropIsSemigroup : ∀ {S : Type ℓ} {_•_} → isProp (IsSemigroup S _•_)
isPropIsSemigroup {_} {_} {_•_} (issemigroup aMagma aAssoc) (issemigroup bMagma bAssoc) =
  cong₂ issemigroup (isPropIsMagma aMagma bMagma) (isPropAssociative (IsMagma.is-set aMagma) _•_ aAssoc bAssoc)

module SemigroupLemmas (S : Semigroup ℓ) where
  open Semigroup S

  ^-sucʳ : ∀ x n → x ^ suc₊₁ n ≡ x ^ n • x
  ^-sucʳ x one    = refl
  ^-sucʳ x (2+ n) =
    x ^ suc₊₁ (2+ n)     ≡⟨⟩
    x ^ 1+ suc (suc n)   ≡⟨⟩
    x • (x • x ^ 1+ n)   ≡⟨⟩
    x • x ^ suc₊₁ (1+ n) ≡⟨ cong (x •_) (^-sucʳ x (1+ n)) ⟩
    x • (x ^ 1+ n • x)   ≡˘⟨ assoc x (x ^ 1+ n) x ⟩
    x • x ^ 1+ n • x     ≡⟨⟩
    x ^ 2+ n • x         ∎

  ^-plus : ∀ x → Homomorphic₂ (x ^_) _+₊₁_ _•_
  ^-plus _ one _ = refl
  ^-plus x (2+ m) n =
    x ^ (1+ (suc m) +₊₁ n) ≡⟨⟩
    x • (x ^ (1+ m +₊₁ n)) ≡⟨ cong (x •_) (^-plus x (1+ m) n) ⟩
    x • (x ^ 1+ m • x ^ n) ≡˘⟨ assoc x (x ^ 1+ m) (x ^ n) ⟩
    x • x ^ 1+ m • x ^ n   ≡⟨⟩
    x ^ 2+ m • x ^ n       ∎

open SemigroupLemmas public
