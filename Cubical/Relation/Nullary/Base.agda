{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Nullary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Functions.Fixpoint

open import Cubical.Relation.Nullary.Decidable public

private
  variable
    ℓ  : Level
    A  : Type ℓ

toWitness : {Q : Dec A} → IsYes Q → A
toWitness {Q = yes x} isYes = x

NonEmpty : Type ℓ → Type ℓ
NonEmpty A = ¬ ¬ A

Stable : Type ℓ → Type ℓ
Stable A = NonEmpty A → A

-- reexport propositional truncation for uniformity
open Cubical.HITs.PropositionalTruncation.Base
  using (∥_∥) public

SplitSupport : Type ℓ → Type ℓ
SplitSupport A = ∥ A ∥ → A

Collapsible : Type ℓ → Type ℓ
Collapsible A = Σ[ f ∈ (A → A) ] 2-Constant f

Populated ⟪_⟫ : Type ℓ → Type ℓ
Populated A = (f : Collapsible A) → Fixpoint (f .fst)
⟪_⟫ = Populated

PStable : Type ℓ → Type ℓ
PStable A = ⟪ A ⟫ → A

onAllPaths : (Type ℓ → Type ℓ) → Type ℓ → Type ℓ
onAllPaths S A = (x y : A) → S (x ≡ y)

Separated : Type ℓ → Type ℓ
Separated = onAllPaths Stable

HSeparated : Type ℓ → Type ℓ
HSeparated = onAllPaths SplitSupport

PStable≡ : Type ℓ → Type ℓ
PStable≡ = onAllPaths PStable

Collapsible≡ : Type ℓ → Type ℓ
Collapsible≡ = onAllPaths Collapsible
