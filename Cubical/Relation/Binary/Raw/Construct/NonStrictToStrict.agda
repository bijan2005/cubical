{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary.Raw

module Cubical.Relation.Binary.Raw.Construct.NonStrictToStrict
  {a ℓ} {A : Type a} (_≤_ : RawRel A ℓ) where

open import Cubical.Relation.Binary.Raw.Properties
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Empty hiding (rec)
open import Cubical.Foundations.Function using (_∘_; flip)
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation hiding (elim)

private
  _≢_ : RawRel A a
  x ≢ y = ¬ (x ≡ y)

------------------------------------------------------------------------
-- _≤_ can be turned into _<_ as follows:

_<_ : RawRel A _
x < y = x ≤ y × x ≢ y

------------------------------------------------------------------------
-- Relationship between relations

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = fst

<⇒≢ : _<_ ⇒ _≢_
<⇒≢ = snd

≤∧≢⇒< : ∀ {x y} → x ≤ y → x ≢ y → x < y
≤∧≢⇒< = _,_

<⇒≱ : Antisymmetric _≤_ → ∀ {x y} → x < y → ¬ (y ≤ x)
<⇒≱ antisym (x≤y , x≢y) y≤x = x≢y (antisym x≤y y≤x)

≤⇒≯ : Antisymmetric _≤_ → ∀ {x y} → x ≤ y → ¬ (y < x)
≤⇒≯ antisym x≤y y<x = <⇒≱ antisym y<x x≤y

≰⇒> : Reflexive _≤_ → Total _≤_ →
      ∀ {x y} → ¬ (x ≤ y) → y < x
≰⇒> rfl total {x} {y} x≰y with total x y
... | inl x≤y = elim (x≰y x≤y)
... | inr y≤x = y≤x , x≰y ∘ reflx→fromeq _≤_ rfl ∘ sym

≮⇒≥ : Discrete A → Reflexive _≤_ → Total _≤_ →
      ∀ {x y} → ¬ (x < y) → y ≤ x
≮⇒≥ _≟_ ≤-refl _≤?_ {x} {y} x≮y with x ≟ y
... | yes x≈y            = reflx→fromeq _≤_ ≤-refl (sym x≈y)
... | no x≢y with y ≤? x
...   | inl y≤x = y≤x
...   | inr x≤y = elim (x≮y (x≤y , x≢y))

------------------------------------------------------------------------
-- Relational properties

<-isPropValued : isPropValued _≤_ → isPropValued _<_
<-isPropValued propv x y = isProp× (propv x y) (isPropΠ λ _ → isProp⊥)

<-toNotEq : ToNotEq _<_
<-toNotEq (_ , x≢y) x≡y = x≢y x≡y

<-irrefl : Irreflexive _<_
<-irrefl = tonoteq→irrefl _<_ <-toNotEq

<-transitive : IsPartialOrder _≤_ → Transitive _<_
<-transitive po (x≤y , x≢y) (y≤z , y≉z) =
  (transitive x≤y y≤z , x≢y ∘ antisym x≤y ∘ transitive y≤z ∘ fromEq ∘ sym)
  where open IsPartialOrder po

<-≤-trans : Transitive _≤_ → Antisymmetric _≤_ →
           Trans _<_ _≤_ _<_
<-≤-trans transitive antisym (x≤y , x≢y) y≤z =
  transitive x≤y y≤z , (λ x≡z → x≢y (antisym x≤y (Respectsʳ≡ _≤_ (sym x≡z) y≤z)))

≤-<-trans : Transitive _≤_ → Antisymmetric _≤_ →
           Trans _≤_ _<_ _<_
≤-<-trans trans antisym x≤y (y≤z , y≢z) =
  trans x≤y y≤z , (λ x≡z → y≢z (antisym y≤z (Respectsˡ≡ _≤_ x≡z x≤y)))

<-asym : Antisymmetric _≤_ → Asymmetric _<_
<-asym antisym (x≤y , x≢y) (y≤x , _) = x≢y (antisym x≤y y≤x)

<-decidable : Discrete A → Decidable _≤_ → Decidable _<_
<-decidable _≟_ _≤?_ x y with x ≤? y
... | no ¬p = no (¬p ∘ fst)
... | yes p with x ≟ y
...   | yes q = no (λ x<y → snd x<y q)
...   | no ¬q = yes (p , ¬q)

------------------------------------------------------------------------
-- Structures

isStrictPartialOrder : IsPartialOrder _≤_ → IsStrictPartialOrder _<_
isStrictPartialOrder po = record
  { irrefl     = <-irrefl
  ; transitive = <-transitive po
  } where open IsPartialOrder po
