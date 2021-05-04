{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Reasoning.Equivalence {c ℓ} (E : Equivalence c ℓ) where

open Equivalence E

------------------------------------------------------------------------
-- Reasoning combinators

open import Cubical.Relation.Binary.Reasoning.PartialEquivalence partialEquivalence public
  hiding (_∎⟨_⟩)
open import Cubical.Relation.Binary.Reasoning.Base.Single _≈_ isPreorder public
  using (_∎)
