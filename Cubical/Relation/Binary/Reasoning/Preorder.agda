{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Reasoning.Preorder {c ℓ} (P : Preorder c ℓ) where

open Preorder P

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Cubical.Relation.Binary.Reasoning.Base.Single _∼_ isPreorder public
