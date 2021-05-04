{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Construct.Unit where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Group
open import Cubical.Data.Prod using (_,_)

open import Cubical.Data.Unit

import Cubical.Algebra.Monoid.Construct.Unit as ⊤Monoid
open ⊤Monoid public hiding (⊤-isMonoid; ⊤-Monoid)

inv : Op₁ ⊤
inv _ = tt

⊤-inverseˡ : LeftInverse tt inv _◯_
⊤-inverseˡ _ = refl

⊤-inverseʳ : RightInverse tt inv _◯_
⊤-inverseʳ _ = refl

⊤-inverse : Inverse tt inv _◯_
⊤-inverse = ⊤-inverseˡ , ⊤-inverseʳ


⊤-isGroup : IsGroup ⊤ _◯_ tt inv
⊤-isGroup = record
  { isMonoid = ⊤Monoid.⊤-isMonoid
  ; inverse  = ⊤-inverse
  }

⊤-Group : Group ℓ-zero
⊤-Group = record { isGroup = ⊤-isGroup }
