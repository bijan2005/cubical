{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Relation.Binary.Definitions where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Data.Maybe.Base using (Maybe)
open import Cubical.Data.Prod.Base using (_×_)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥)
open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary.Decidable

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type a
    B : Type b
    C : Type c

infix 8 _⟶_Respects_ _Respects_ _Respectsˡ_ _Respectsʳ_ _Respects₂_

------------------------------------------------------------------------
-- Definitions
------------------------------------------------------------------------

-- Reflexivity.

Reflexive : Rel A ℓ → Type _
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Equality can be converted to proof of relation.

FromEq : Rel A ℓ → Type _
FromEq _∼_ = _≡_ ⇒ _∼_

-- Irreflexivity.

Irreflexive : Rel A ℓ → Type _
Irreflexive _<_ = ∀ {x} → ¬ (x < x)

-- Relation implies inequality.

ToNotEq : Rel A ℓ → Type _
ToNotEq _<_ = _<_ ⇒ (λ x y → ¬ (x ≡ y))

-- Generalised symmetry.

Sym : REL A B ℓ₁ → REL B A ℓ₂ → Type _
Sym P Q = P ⇒ flip Q

-- Symmetry.

Symmetric : Rel A ℓ → Type _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Type _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

-- A flipped variant of generalised transitivity.

TransFlip : REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Type _
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

-- Transitivity.

Transitive : Rel A ℓ → Type _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- Generalised antisymmetry.

Antisym : REL A B ℓ₁ → REL B A ℓ₂ → REL A B ℓ₃ → Type _
Antisym R S E = ∀ {i j} → R i j → S j i → E i j

-- Antisymmetry.

Antisymmetric : Rel A ℓ → Type _
Antisymmetric _≤_ = Antisym _≤_ _≤_ _≡_

-- Asymmetry.

Asymmetric : Rel A ℓ → Type _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

-- Generalised connex - exactly one of the two relations holds.

Connex : REL A B ℓ₁ → REL B A ℓ₂ → Type _
Connex P Q = ∀ x y → P x y ⊎ Q y x

-- Totality.

Total : Rel A ℓ → Type _
Total _∼_ = Connex _∼_ _∼_

-- Truncated connex - Preserves propositions.

PropConnex : REL A B ℓ₁ → REL B A ℓ₂ → Type _
PropConnex P Q = ∀ x y → ∥ P x y ⊎ Q y x ∥

-- Truncated totality.

PropTotal : Rel A ℓ → Type _
PropTotal _∼_ = PropConnex _∼_ _∼_

-- Generalised trichotomy - exactly one of three types has a witness.

data Tri (A : Type a) (B : Type b) (C : Type c) : Type (ℓ-max a (ℓ-max b c)) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≡ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

-- Trichotomy.

Trichotomous : Rel A ℓ → Type _
Trichotomous _<_ = ∀ x y → Tri (x < y) (x ≡ y) (x > y)
  where _>_ = flip _<_

-- Generalised maximum element.

Max : REL A B ℓ → B → Type _
Max _≤_ T = ∀ x → x ≤ T

-- Maximum element.

Maximum : Rel A ℓ → A → Type _
Maximum = Max

-- Generalised minimum element.

Min : REL A B ℓ → A → Type _
Min R = Max (flip R)

-- Minimum element.

Minimum : Rel A ℓ → A → Type _
Minimum = Min

-- Unary relations respecting a binary relation.

_⟶_Respects_ : (A → Type ℓ₁) → (B → Type ℓ₂) → REL A B ℓ₃ → Type _
P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

-- Unary relation respects a binary relation.

_Respects_ : (A → Type ℓ₁) → Rel A ℓ₂ → Type _
P Respects _∼_ = P ⟶ P Respects _∼_

-- Right respecting - relatedness is preserved on the right by some equivalence.

_Respectsʳ_ : REL A B ℓ₁ → Rel B ℓ₂ → Type _
_∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_

-- Left respecting - relatedness is preserved on the left by some equivalence.

_Respectsˡ_ : REL A B ℓ₁ → Rel A ℓ₂ → Type _
_∼_ Respectsˡ _≈_ = ∀ {y} → (_∼ y) Respects _≈_

-- Respecting - relatedness is preserved on both sides by some equivalence.

_Respects₂_ : Rel A ℓ₁ → Rel A ℓ₂ → Type _
_∼_ Respects₂ _≈_ = (_∼_ Respectsʳ _≈_) × (_∼_ Respectsˡ _≈_)

-- Substitutivity - any two related elements satisfy exactly the same
-- set of unary relations. Note that only the various derivatives
-- of propositional equality can satisfy this property.

Substitutive : Rel A ℓ₁ → (ℓ₂ : Level) → Type _
Substitutive {A = A} _∼_ p = (P : A → Type p) → P Respects _∼_

-- Decidability - it is possible to determine whether a given pair of
-- elements are related.

Decidable : REL A B ℓ → Type _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- Weak decidability - it is sometimes possible to determine if a given
-- pair of elements are related.

WeaklyDecidable : REL A B ℓ → Type _
WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)

-- Universal - all pairs of elements are related

Universal : REL A B ℓ → Type _
Universal _∼_ = ∀ x y → x ∼ y

-- Non-emptiness - at least one pair of elements are related.

record NonEmpty {A : Type a} {B : Type b}
                (T : REL A B ℓ) : Type (ℓ-max a (ℓ-max b ℓ)) where
  constructor nonEmpty
  field
    {x}   : A
    {y}   : B
    proof : T x y
