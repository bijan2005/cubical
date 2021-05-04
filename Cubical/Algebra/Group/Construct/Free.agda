{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Group.Construct.Free {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Algebra.Group

open import Cubical.Data.Empty.Polymorphic
open import Cubical.Data.Prod

open import Cubical.Relation.Binary.Reasoning.Equality

A = ⟨ Aˢ ⟩
isSetA = Aˢ .snd

data FreeG : Type ℓ where
  inj : A → FreeG
  _•_ : Op₂ FreeG
  ε   : FreeG
  _⁻¹ : Op₁ FreeG

  •-assoc     : Associative _•_
  •-identityˡ : LeftIdentity ε _•_
  •-identityʳ : RightIdentity ε _•_
  •-inverseˡ  : LeftInverse ε _⁻¹ _•_
  •-inverseʳ  : RightInverse ε _⁻¹ _•_

  squash : isSet FreeG

•-identity : Identity ε _•_
•-identity = •-identityˡ , •-identityʳ

•-inverse : Inverse ε _⁻¹ _•_
•-inverse = •-inverseˡ , •-inverseʳ


elim : ∀ {ℓ′} {B : FreeG → Type ℓ′} →
        (∀ x → isSet (B x)) →
        (∀ x → B (inj x)) →
        (op : ∀ {x y} → B x → B y → B (x • y)) →
        (e : B ε) →
        (inv : ∀ {x} → B x → B (x ⁻¹)) →
        (∀ {x y z} (a : B x) (b : B y) (c : B z) → PathP (λ i → B (•-assoc x y z i)) (op (op a b) c) (op a (op b c))) →
        (∀ {x} (a : B x) → PathP (λ i → B (•-identityˡ x i)) (op e a) a) →
        (∀ {x} (a : B x) → PathP (λ i → B (•-identityʳ x i)) (op a e) a) →
        (∀ {x} (a : B x) → PathP (λ i → B (•-inverseˡ x i)) (op (inv a) a) e) →
        (∀ {x} (a : B x) → PathP (λ i → B (•-inverseʳ x i)) (op a (inv a)) e) →
        (x : FreeG) → B x
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (inj x) = f x
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (x • y) = op (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x)
                                                            (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ y)
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ ε = e
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (x ⁻¹) = inv (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x)
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (•-assoc x y z i) = assc (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x)
                                                                        (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ y)
                                                                        (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ z) i
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (•-identityˡ x i) = idˡ (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x) i
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (•-identityʳ x i) = idʳ (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x) i
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (•-inverseˡ x i) = invˡ (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x) i
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (•-inverseʳ x i) = invʳ (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x) i
elim isSetB f op e inv assc idˡ idʳ invˡ invʳ (squash x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 isSetB
    (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ x) (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ y)
    (cong (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ) p) (cong (elim isSetB f op e inv assc idˡ idʳ invˡ invʳ) q) (squash x y p q) i j


FreeG-isGroup : IsGroup FreeG _•_ ε _⁻¹
FreeG-isGroup = record
  { isMonoid = record
      { isSemigroup = record
          { isMagma = record { is-set = squash }
          ; assoc   = •-assoc
          }
      ; identity    = •-identity
      }
  ; inverse  = •-inverse
  }

FreeGroup : Group ℓ
FreeGroup = record { isGroup = FreeG-isGroup }
