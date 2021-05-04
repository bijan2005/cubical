{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Construct.Never where

open import Cubical.Core.Everything

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Construct.Constant
open import Cubical.Data.Empty.Polymorphic using (⊥)

------------------------------------------------------------------------
-- Definition

Never : ∀ {a ℓ} {A : Type a} → Rel A ℓ
Never = Const ⊥
