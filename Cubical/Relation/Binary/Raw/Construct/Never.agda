{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Raw.Construct.Never where

open import Cubical.Core.Everything

open import Cubical.Relation.Binary.Raw
open import Cubical.Relation.Binary.Raw.Construct.Constant
open import Cubical.Data.Empty.Polymorphic using (⊥)

------------------------------------------------------------------------
-- Definition

Never : ∀ {a ℓ} {A : Type a} → RawRel A ℓ
Never = Const ⊥
