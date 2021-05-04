{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Unary where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (isProp)

open import Cubical.Data.Empty hiding (rec)
open import Cubical.Data.Unit.Base using (⊤)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base using (_⊎_; rec)
open import Cubical.Foundations.Function

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Decidable using (IsYes)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Type a
    B : Type b
    C : Type c

------------------------------------------------------------------------
-- Definition

-- Unary relations are known as predicates and `Pred A ℓ` can be viewed
-- as some property that elements of type A might satisfy.

-- Consequently `P : Pred A ℓ` can also be seen as a subset of A
-- containing all the elements of A that satisfy property P. This view
-- informs much of the notation used below.

Pred : Type a → (ℓ : Level) → Type _
Pred A ℓ = A → Type ℓ

isPropValued : Pred A ℓ → Type _
isPropValued P = ∀ x → isProp (P x)

PropPred : Type a → (ℓ : Level) → Type _
PropPred A ℓ = Σ (Pred A ℓ) isPropValued

⟨_⟩ᴾ : PropPred A ℓ → Pred A ℓ
⟨_⟩ᴾ = fst

------------------------------------------------------------------------
-- Special sets

-- The empty set.

∅ : Pred A _
∅ = λ _ → ⊥

-- The singleton set.

｛_｝ : A → Pred A _
｛ x ｝ = _≡ x

-- The universal set.

U : Pred A _
U = λ _ → ⊤

------------------------------------------------------------------------
-- Membership

infix 6 _∈_ _∉_

_∈_ : A → Pred A ℓ → Type _
x ∈ P = P x

_∉_ : A → Pred A ℓ → Type _
x ∉ P = ¬ x ∈ P

------------------------------------------------------------------------
-- Subset relations

infix 6 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_

_⊆_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊇ Q = Q ⊆ P

_⊈_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊈ Q = ¬ (P ⊆ Q)

_⊉_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊉ Q = ¬ (P ⊇ Q)

_⊂_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊂ Q = P ⊆ Q × Q ⊈ P

_⊃_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊃ Q = Q ⊂ P

_⊄_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊄ Q = ¬ (P ⊂ Q)

_⊅_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⊅ Q = ¬ (P ⊃ Q)

------------------------------------------------------------------------
-- Properties of sets

infix 10 Satisfiable Universal IUniversal

-- Emptiness - no element satisfies P.

Empty : Pred A ℓ → Type _
Empty P = ∀ x → x ∉ P

-- Satisfiable - at least one element satisfies P.

Satisfiable : Pred A ℓ → Type _
Satisfiable {A = A} P = ∃[ x ∈ A ] x ∈ P

syntax Satisfiable P = ∃⟨ P ⟩

-- Universality - all elements satisfy P.

Universal : Pred A ℓ → Type _
Universal P = ∀ x → x ∈ P

syntax Universal P = Π[ P ]

-- Implicit universality - all elements satisfy P.

IUniversal : Pred A ℓ → Type _
IUniversal P = ∀ {x} → x ∈ P

syntax IUniversal P = ∀[ P ]

-- Decidability - it is possible to determine if an arbitrary element
-- satisfies P.

Decidable : Pred A ℓ → Type _
Decidable P = ∀ x → Dec (P x)

------------------------------------------------------------------------
-- Operations on sets

infix 10 ⋃ ⋂
infixr 9 _⊢_
infixr 8 _⇒_
infixr 7 _∩_
infixr 6 _∪_
infix 5 _≬_

-- Complement.

∁ : Pred A ℓ → Pred A ℓ
∁ P = λ x → x ∉ P

-- Implication.

_⇒_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ⇒ Q = λ x → x ∈ P → x ∈ Q

-- Union.

_∪_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

-- Intersection.

_∩_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∩ Q = λ x → x ∈ P × x ∈ Q

-- Infinitary union.

⋃ : ∀ {i} (I : Type i) → (I → Pred A ℓ) → Pred A _
⋃ I P = λ x → Σ[ i ∈ I ] P i x

syntax ⋃ I (λ i → P) = ⋃[ i ∶ I ] P

-- Infinitary intersection.

⋂ : ∀ {i} (I : Type i) → (I → Pred A ℓ) → Pred A _
⋂ I P = λ x → (i : I) → P i x

syntax ⋂ I (λ i → P) = ⋂[ i ∶ I ] P

-- Positive version of non-disjointness, dual to inclusion.

_≬_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
_≬_ {A = A} P Q = ∃[ x ∈ A ] x ∈ P × x ∈ Q

-- Preimage.

_⊢_ : (A → B) → Pred B ℓ → Pred A ℓ
f ⊢ P = λ x → P (f x)

------------------------------------------------------------------------
-- Preservation under operations

_Preserves_⟶_ : (A → B) → Pred A ℓ₁ → Pred B ℓ₂ → Type _
f Preserves P ⟶ Q = P ⊆ f ⊢ Q

_Preserves_ : (A → A) → Pred A ℓ → Type _
f Preserves P = f Preserves P ⟶ P

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Pred A ℓ₁ → Pred B ℓ₂ → Pred C ℓ → Type _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y} → x ∈ P → y ∈ Q → x ∙ y ∈ R

_Preserves₂_ : (A → A → A) → Pred A ℓ → Type _
_∙_ Preserves₂ P = _∙_ Preserves₂ P ⟶ P ⟶ P

------------------------------------------------------------------------
-- Logical equivalence

_⇔_ : Pred A ℓ₁ → Pred A ℓ₂ → Type _
P ⇔ Q = Π[ P ⇒ Q ∩ Q ⇒ P ]

------------------------------------------------------------------------
-- Predicate combinators

-- These differ from the set operations above, as the carrier set of the
-- resulting predicates are not the same as the carrier set of the
-- component predicates.

infixr  2 _⟨×⟩_
infixr  2 _⟨⊙⟩_
infixr  1 _⟨⊎⟩_
infixr  0 _⟨→⟩_
infixl  9 _⟨·⟩_
infix  10 _~
infixr  9 _⟨∘⟩_
infixr  2 _//_ _\\_

-- Product.

_⟨×⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨×⟩ Q) (x , y) = x ∈ P × y ∈ Q

-- Sum over one element.

_⟨⊎⟩_ : Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = rec P Q

-- Sum over two elements.

_⟨⊙⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨⊙⟩ Q) (x , y) = x ∈ P ⊎ y ∈ Q

-- Implication.

_⟨→⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = f Preserves P ⟶ Q

-- Product.

_⟨·⟩_ : (P : Pred A ℓ₁) (Q : Pred B ℓ₂) →
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry (flip _$_)
(P ⟨·⟩ Q) (p , f) = f p

-- Converse.

_~ : Pred (A × B) ℓ → Pred (B × A) ℓ
P ~ = P ∘ λ { (x , y) → y , x }

-- Composition.

_⟨∘⟩_ : Pred (A × B) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × C) _
_⟨∘⟩_ {B = B} P Q (x , z) = ∃[ y ∈ B ] (x , y) ∈ P × (y , z) ∈ Q

-- Post-division.

_//_ : Pred (A × C) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × B) _
(P // Q) (x , y) = Q ∘ (y ,_) ⊆ P ∘ (x ,_)

-- Pre-division.

_\\_ : Pred (A × C) ℓ₁ → Pred (A × B) ℓ₂ → Pred (B × C) _
P \\ Q = (P ~ // Q ~) ~
