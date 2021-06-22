{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Relation.Binary.Definitions where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Logic hiding (_⇒_; _⇔_; ¬_)
open import Cubical.Foundations.HLevels

open import Cubical.Data.Maybe.Base using (Maybe)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Sigma.Base
open import Cubical.HITs.PropositionalTruncation.Base

open import Cubical.Relation.Binary.Base
open import Cubical.Relation.Nullary.Decidable

private
  variable
    a b c ℓ ℓ′ ℓ′′ ℓ′′′ : Level
    A : Type a
    B : Type b
    C : Type c


------------------------------------------------------------------------
-- Basic defintions
------------------------------------------------------------------------


infix 7 _⇒_ _⇔_ _=[_]⇒_
infix 8 _⟶_Respects_ _Respects_ _Respectsˡ_ _Respectsʳ_ _Respects₂_

idRel : (A : Type ℓ) → Rel A ℓ
idRel A a b .fst = ∥ a ≡ b ∥
idRel A _ _ .snd = squash

invRel : REL A B ℓ′ → REL B A ℓ′
invRel R b a = R a b

compRel : REL A B ℓ′ → REL B C ℓ′′ → REL A C _
compRel R S a c .fst = ∃[ b ∈ _ ] ⟨ R a b ⟩ × ⟨ S b c ⟩
compRel R S _ _ .snd = squash

graphRel : {B : Type b} → (A → B) → isSet B → REL A B b
graphRel f isSetB a b .fst = f a ≡ b
graphRel f isSetB a b .snd = isSetB (f a) b


-- Implication/containment - could also be written _⊆_.
-- and corresponding notion of equivalence

_⇒_ : REL A B ℓ → REL A B ℓ′ → Type _
P ⇒ Q = ∀ {x y} → ⟨ P x y ⟩ → ⟨ Q x y ⟩

_⇔_ : REL A B ℓ → REL A B ℓ′ → Type _
P ⇔ Q = P ⇒ Q × Q ⇒ P

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : Rel A ℓ → (A → B) → Rel B ℓ′ → Type _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ → Rel B ℓ′ → Type _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- An endomorphic variant of _Preserves_⟶_.

_Preserves_ : (A → A) → Rel A ℓ → Type _
f Preserves P = f Preserves P ⟶ P

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ → Rel B ℓ′ → Rel C ℓ′′ → Type _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → ⟨ P x y ⟩ → ⟨ Q u v ⟩ → ⟨ R (x ∙ u) (y ∙ v) ⟩


------------------------------------------------------------------------
-- Property predicates
------------------------------------------------------------------------

-- Reflexivity.

Reflexive : Rel A ℓ → Type _
Reflexive _∼_ = ∀ {x} → ⟨ x ∼ x ⟩

-- Equality can be converted to proof of relation.

FromEq : Rel A ℓ → Type _
FromEq _∼_ = _≡ₚ_ ⇒ _∼_

-- Irreflexivity.

Irreflexive : Rel A ℓ → Type _
Irreflexive _<_ = ∀ {x} → ¬ ⟨ x < x ⟩

-- Relation implies inequality.

ToNotEq : Rel A ℓ → Type _
ToNotEq _<_ = _<_ ⇒ _≢ₚ_

-- Generalised symmetry.

Sym : REL A B ℓ → REL B A ℓ′ → Type _
Sym P Q = P ⇒ flip Q

-- Symmetry.

Symmetric : Rel A ℓ → Type _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : REL A B ℓ → REL B C ℓ′ → REL A C ℓ′′ → Type _
Trans P Q R = ∀ {i j k} → ⟨ P i j ⟩ → ⟨ Q j k ⟩ → ⟨ R i k ⟩

-- A flipped variant of generalised transitivity.

TransFlip : REL A B ℓ → REL B C ℓ′ → REL A C ℓ′′ → Type _
TransFlip P Q R = ∀ {i j k} → ⟨ Q j k ⟩ → ⟨ P i j ⟩ → ⟨ R i k ⟩

-- Transitivity.

Transitive : Rel A ℓ → Type _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- Generalised antisymmetry.

Antisym : REL A B ℓ → REL B A ℓ′ → REL A B ℓ′′ → Type _
Antisym R S E = ∀ {i j} → ⟨ R i j ⟩ → ⟨ S j i ⟩ → ⟨ E i j ⟩

-- Antisymmetry.

Antisymmetric : Rel A ℓ → Type _
Antisymmetric _≤_ = Antisym _≤_ _≤_ _≡ₚ_

-- Asymmetry.

Asymmetric : Rel A ℓ → Type _
Asymmetric _<_ = ∀ {x y} → ⟨ x < y ⟩ → ¬ ⟨ y < x ⟩

-- Generalised connex - exactly one of the two relations holds.

RawConnex : REL A B ℓ → REL B A ℓ′ → Type _
RawConnex P Q = ∀ x y → ⟨ P x y ⟩ ⊎ ⟨ Q y x ⟩

-- Totality.

RawTotal : Rel A ℓ → Type _
RawTotal _∼_ = RawConnex _∼_ _∼_

-- Truncated connex - Preserves propositions.

Connex : REL A B ℓ → REL B A ℓ′ → Type _
Connex P Q = ∀ x y → ⟨ P x y ⊔ Q y x ⟩

-- Truncated totality.

Total : Rel A ℓ → Type _
Total _∼_ = Connex _∼_ _∼_

-- Generalised trichotomy - exactly one of three types has a witness.

data Tri (A : Type a) (B : Type b) (C : Type c) : Type (ℓ-max a (ℓ-max b c)) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≡ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

-- Trichotomy.

Trichotomous : Rel A ℓ → Type _
Trichotomous _<_ = ∀ x y → Tri ⟨ x < y ⟩ (x ≡ y) ⟨ x > y ⟩
  where _>_ = flip _<_

-- Maximum element.

Maximum : REL A B ℓ → B → Type _
Maximum _≤_ g = ∀ x → ⟨ x ≤ g ⟩

-- Minimum element

Minimum : REL A B ℓ → A → Type _
Minimum _≤_ l = ∀ x → ⟨ l ≤ x ⟩

-- Unary relations respecting a binary relation.

_⟶_Respects_ : (A → hProp ℓ) → (B → hProp ℓ′) → REL A B ℓ′′ → Type _
P ⟶ Q Respects _∼_ = ∀ {x y} → ⟨ x ∼ y ⟩ → ⟨ P x ⟩ → ⟨ Q y ⟩

-- Unary relation respects a binary relation.

_Respects_ : (A → hProp ℓ) → Rel A ℓ′ → Type _
P Respects _∼_ = P ⟶ P Respects _∼_

-- Right respecting - relatedness is preserved on the right by some equivalence.

_Respectsʳ_ : REL A B ℓ → Rel B ℓ′ → Type _
_∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_

-- Left respecting - relatedness is preserved on the left by some equivalence.

_Respectsˡ_ : REL A B ℓ → Rel A ℓ′ → Type _
_∼_ Respectsˡ _≈_ = ∀ {y} → (_∼ y) Respects _≈_

-- Respecting - relatedness is preserved on both sides by some equivalence.

_Respects₂_ : Rel A ℓ → Rel A ℓ′ → Type _
_∼_ Respects₂ _≈_ = (_∼_ Respectsʳ _≈_) × (_∼_ Respectsˡ _≈_)

-- Substitutivity - any two related elements satisfy exactly the same
-- set of unary relations. Note that only the various derivatives
-- of propositional equality can satisfy this property.

Substitutive : Rel A ℓ → (ℓ′ : Level) → Type _
Substitutive {A = A} _∼_ p = (P : A → hProp p) → P Respects _∼_

-- Decidability - it is possible to determine whether a given pair of
-- elements are related.

Decidable : REL A B ℓ → Type _
Decidable _∼_ = ∀ x y → Dec ⟨ x ∼ y ⟩

-- Weak decidability - it is sometimes possible to determine if a given
-- pair of elements are related.

WeaklyDecidable : REL A B ℓ → Type _
WeaklyDecidable _∼_ = ∀ x y → Maybe ⟨ x ∼ y ⟩

-- Universal - all pairs of elements are related

Universal : REL A B ℓ → Type _
Universal _∼_ = ∀ x y → ⟨ x ∼ y ⟩

-- Non-emptiness - at least one pair of elements are related.

NonEmpty : REL A B ℓ → Type _
NonEmpty _∼_ = ∃[ x ∈ _ ] ∃[ y ∈ _ ] ⟨ x ∼ y ⟩
