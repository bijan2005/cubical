{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Relation.Binary.Raw.Definitions where

open import Cubical.Core.Everything

open import Cubical.Foundations.Function
open import Cubical.Data.Maybe.Base using (Maybe)
open import Cubical.Data.Prod.Base using (_×_)
open import Cubical.Data.Sigma.Base using (∃-syntax)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.HITs.PropositionalTruncation.Base using (∥_∥)

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary.Decidable

private
  variable
    a b c ℓ ℓ′ ℓ′′ : Level
    A : Type a
    B : Type b
    C : Type c

infix 8 _⟶_Respects_ _Respects_ _Respectsˡ_ _Respectsʳ_ _Respects₂_


------------------------------------------------------------------------
-- Basic definitions
------------------------------------------------------------------------

idRel : (A : Type ℓ) → RawRel A ℓ
idRel A a b = a ≡ b

invRel : ∀ {A B : Type ℓ} → RawREL A B ℓ′ → RawREL B A ℓ′
invRel R b a = R a b

compRel : ∀ {A B C : Type ℓ} → RawREL A B ℓ′ → RawREL B C ℓ′′ → RawREL A C _
compRel R S a c = Σ[ b ∈ _ ] (R a b × S b c)

graphRel : ∀ {A B : Type ℓ} → (A → B) → RawREL A B ℓ
graphRel f a b = f a ≡ b


infix 7 _⇒_ _⇔_ _=[_]⇒_

-- Implication/containment - could also be written _⊆_.
-- and corresponding notion of equivalence

_⇒_ : RawREL A B ℓ → RawREL A B ℓ′ → Type _
P ⇒ Q = ∀ {x y} → P x y → Q x y

_⇔_ : RawREL A B ℓ → RawREL A B ℓ′ → Type _
P ⇔ Q = P ⇒ Q × Q ⇒ P

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : RawRel A ℓ → (A → B) → RawRel B ℓ′ → Type _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → RawRel A ℓ → RawRel B ℓ′ → Type _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- An endomorphic variant of _Preserves_⟶_.

_Preserves_ : (A → A) → RawRel A ℓ → Type _
f Preserves P = f Preserves P ⟶ P

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → RawRel A ℓ → RawRel B ℓ′ → RawRel C ℓ′′ → Type _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)


------------------------------------------------------------------------
-- Property predicates
------------------------------------------------------------------------

-- Reflexivity.

Reflexive : RawRel A ℓ → Type _
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Equality can be converted to proof of relation.

FromEq : RawRel A ℓ → Type _
FromEq _∼_ = _≡_ ⇒ _∼_

-- Irreflexivity.

Irreflexive : RawRel A ℓ → Type _
Irreflexive _<_ = ∀ {x} → ¬ (x < x)

-- Relation implies inequality.

ToNotEq : RawRel A ℓ → Type _
ToNotEq _<_ = _<_ ⇒ (λ x y → ¬ (x ≡ y))

-- Generalised symmetry.

Sym : RawREL A B ℓ → RawREL B A ℓ′ → Type _
Sym P Q = P ⇒ flip Q

-- Symmetry.

Symmetric : RawRel A ℓ → Type _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : RawREL A B ℓ → RawREL B C ℓ′ → RawREL A C ℓ′′ → Type _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

-- A flipped variant of generalised transitivity.

TransFlip : RawREL A B ℓ → RawREL B C ℓ′ → RawREL A C ℓ′′ → Type _
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

-- Transitivity.

Transitive : RawRel A ℓ → Type _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- Generalised antisymmetry.

Antisym : RawREL A B ℓ → RawREL B A ℓ′ → RawREL A B ℓ′′ → Type _
Antisym R S E = ∀ {i j} → R i j → S j i → E i j

-- Antisymmetry.

Antisymmetric : RawRel A ℓ → Type _
Antisymmetric _≤_ = Antisym _≤_ _≤_ _≡_

-- Asymmetry.

Asymmetric : RawRel A ℓ → Type _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

-- Generalised connex - exactly one of the two relations holds.

Connex : RawREL A B ℓ → RawREL B A ℓ′ → Type _
Connex P Q = ∀ x y → P x y ⊎ Q y x

-- Totality.

Total : RawRel A ℓ → Type _
Total _∼_ = Connex _∼_ _∼_

-- Truncated connex - Preserves propositions.

PropConnex : RawREL A B ℓ → RawREL B A ℓ′ → Type _
PropConnex P Q = ∀ x y → ∥ P x y ⊎ Q y x ∥

-- Truncated totality.

PropTotal : RawRel A ℓ → Type _
PropTotal _∼_ = PropConnex _∼_ _∼_

-- Generalised trichotomy - exactly one of three types has a witness.

data Tri (A : Type a) (B : Type b) (C : Type c) : Type (ℓ-max a (ℓ-max b c)) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≡ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

-- Trichotomy.

Trichotomous : RawRel A ℓ → Type _
Trichotomous _<_ = ∀ x y → Tri (x < y) (x ≡ y) (x > y)
  where _>_ = flip _<_

-- Generalised maximum element.

Max : RawREL A B ℓ → B → Type _
Max _≤_ T = ∀ x → x ≤ T

-- Maximum element.

Maximum : RawRel A ℓ → A → Type _
Maximum = Max

-- Generalised minimum element.

Min : RawREL A B ℓ → A → Type _
Min R = Max (flip R)

-- Minimum element.

Minimum : RawRel A ℓ → A → Type _
Minimum = Min

-- Unary relations respecting a binary relation.

_⟶_Respects_ : (A → Type ℓ) → (B → Type ℓ′) → RawREL A B ℓ′′ → Type _
P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

-- Unary relation respects a binary relation.

_Respects_ : (A → Type ℓ) → RawRel A ℓ′ → Type _
P Respects _∼_ = P ⟶ P Respects _∼_

-- Right respecting - relatedness is preserved on the right by some equivalence.

_Respectsʳ_ : RawREL A B ℓ → RawRel B ℓ′ → Type _
_∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_

-- Left respecting - relatedness is preserved on the left by some equivalence.

_Respectsˡ_ : RawREL A B ℓ → RawRel A ℓ′ → Type _
_∼_ Respectsˡ _≈_ = ∀ {y} → (_∼ y) Respects _≈_

-- Respecting - relatedness is preserved on both sides by some equivalence.

_Respects₂_ : RawRel A ℓ → RawRel A ℓ′ → Type _
_∼_ Respects₂ _≈_ = (_∼_ Respectsʳ _≈_) × (_∼_ Respectsˡ _≈_)

-- Substitutivity - any two related elements satisfy exactly the same
-- set of unary relations. Note that only the various derivatives
-- of propositional equality can satisfy this property.

Substitutive : RawRel A ℓ → (ℓ′ : Level) → Type _
Substitutive {A = A} _∼_ p = (P : A → Type p) → P Respects _∼_

-- Decidability - it is possible to determine whether a given pair of
-- elements are related.

Decidable : RawREL A B ℓ → Type _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- Weak decidability - it is sometimes possible to determine if a given
-- pair of elements are related.

WeaklyDecidable : RawREL A B ℓ → Type _
WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)

-- Universal - all pairs of elements are related

Universal : RawREL A B ℓ → Type _
Universal _∼_ = ∀ x y → x ∼ y

-- Non-emptiness - at least one pair of elements are related.

NonEmpty : RawREL A B ℓ → Type _
NonEmpty _∼_ = ∃[ x ∈ _ ] ∃[ y ∈ _ ] x ∼ y
