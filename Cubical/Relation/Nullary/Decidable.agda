{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Nullary.Decidable where

open import Cubical.Core.Everything
open import Cubical.Data.Empty using (⊥)

private
  variable
    ℓ : Level

-- Negation
infix 3 ¬_

¬_ : Type ℓ → Type ℓ
¬ A = A → ⊥

-- Decidable types (inspired by standard library)
data Dec (P : Type ℓ) : Type ℓ where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P

data IsYes {P : Type ℓ} : Dec P → Type ℓ where
  isYes : ∀ {x} → IsYes (yes x)

Discrete : Type ℓ → Type ℓ
Discrete A = ∀ x y → Dec (Path A x y)
