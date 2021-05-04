{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Reasoning.PartialOrder
  {c ℓ} (P : PartialOrder c ℓ) where

open PartialOrder P
import Cubical.Relation.Binary.Construct.NonStrictToStrict _≤_ as Strict

------------------------------------------------------------------------
-- Re-export contents of base module

open import Cubical.Relation.Binary.Reasoning.Base.Double
  isPreorder
  (Strict.<-transitive isPartialOrder)
  Strict.<⇒≤
  (Strict.<-≤-trans transitive antisym)
  (Strict.≤-<-trans transitive antisym)
  public
