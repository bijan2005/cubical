{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Binary.Base where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_on_)
open import Cubical.Data.Sigma.Base
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.PropositionalTruncation.Base

private
  variable
    a b c ℓ ℓ' ℓ'' ℓ''' : Level
    A : Type a
    B : Type b
    C : Type c

REL : Type a → Type b → (ℓ : Level) → Type _
REL A B ℓ = A → B → Type ℓ

Rel : Type a → (ℓ : Level) → Type _
Rel A ℓ = REL A A ℓ

isPropValued : {A : Type a} {B : Type b} → REL A B ℓ → Type _
isPropValued R = ∀ a b → isProp (R a b)

PropREL : Type a → Type b → (ℓ : Level) → Type _
PropREL A B ℓ = Σ (REL A B ℓ) isPropValued

PropRel : Type a → (ℓ : Level) → Type _
PropRel A ℓ = PropREL A A ℓ

⟨_⟩ᴿ : PropREL A B ℓ → REL A B ℓ
⟨_⟩ᴿ = fst

⟨_⟩ᵖ : (R : PropREL A B ℓ) → isPropValued ⟨ R ⟩ᴿ
⟨_⟩ᵖ = snd

idPropRel : (A : Type ℓ) → PropRel A ℓ
idPropRel A .fst a a' = ∥ a ≡ a' ∥
idPropRel A .snd _ _ = squash

invPropRel : ∀ {A B : Type ℓ}
  → PropREL A B ℓ' → PropREL B A ℓ'
invPropRel R .fst b a = R .fst a b
invPropRel R .snd b a = R .snd a b

compPropRel : ∀ {A B C : Type ℓ}
  → PropREL A B ℓ' → PropREL B C ℓ'' → PropREL A C _
compPropRel R S .fst a c = ∥ Σ[ b ∈ _ ] (R .fst a b × S .fst b c) ∥
compPropRel R S .snd _ _ = squash

graphRel : ∀ {A B : Type ℓ} → (A → B) → REL A B ℓ
graphRel f a b = f a ≡ b

infix 7 _⇒_ _⇔_ _=[_]⇒_

-- Implication/containment - could also be written _⊆_.
-- and corresponding notion of equivalence

_⇒_ : REL A B ℓ → REL A B ℓ' → Type _
P ⇒ Q = ∀ {x y} → P x y → Q x y

_⇔_ : REL A B ℓ → REL A B ℓ' → Type _
P ⇔ Q = P ⇒ Q × Q ⇒ P

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : Rel A ℓ → (A → B) → Rel B ℓ' → Type _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ → Rel B ℓ' → Type _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- An endomorphic variant of _Preserves_⟶_.

_Preserves_ : (A → A) → Rel A ℓ → Type _
f Preserves P = f Preserves P ⟶ P

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ → Rel B ℓ' → Rel C ℓ'' → Type _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)
