{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Monoid.Construct.Free {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Algebra.Monoid

open import Cubical.Data.Empty.Polymorphic
open import Cubical.Data.Prod

open import Cubical.Relation.Binary.Reasoning.Equality

private
  A = ⟨ Aˢ ⟩
  isSetA = Aˢ .snd

------------------------------------------------------------------------
-- The direct free monoid type

data FreeM : Type ℓ where
  inj : A → FreeM
  _•_ : Op₂ FreeM
  ε   : FreeM

  •-assoc     : Associative _•_
  ε-identityˡ : LeftIdentity ε _•_
  ε-identityʳ : RightIdentity ε _•_

  squash : isSet FreeM

ε-identity : Identity ε _•_
ε-identity = ε-identityˡ , ε-identityʳ

elim : ∀ {ℓ′} {B : FreeM → Type ℓ′} →
        (∀ x → isSet (B x)) →
        (∀ x → B (inj x)) →
        (op : ∀ {x y} → B x → B y → B (x • y)) →
        (e : B ε) →
        (∀ {x y z} (a : B x) (b : B y) (c : B z) → PathP (λ i → B (•-assoc x y z i)) (op (op a b) c) (op a (op b c))) →
        (∀ {x} (a : B x) → PathP (λ i → B (ε-identityˡ x i)) (op e a) a) →
        (∀ {x} (a : B x) → PathP (λ i → B (ε-identityʳ x i)) (op a e) a) →
        (x : FreeM) → B x
elim isSetB f op e assc idˡ idʳ (inj x) = f x
elim isSetB f op e assc idˡ idʳ (x • y) = op (elim isSetB f op e assc idˡ idʳ x) (elim isSetB f op e assc idˡ idʳ y)
elim isSetB f op e assc idˡ idʳ ε = e
elim isSetB f op e assc idˡ idʳ (•-assoc x y z i) = assc (elim isSetB f op e assc idˡ idʳ x)
                                                          (elim isSetB f op e assc idˡ idʳ y)
                                                          (elim isSetB f op e assc idˡ idʳ z) i
elim isSetB f op e assc idˡ idʳ (ε-identityˡ x i) = idˡ (elim isSetB f op e assc idˡ idʳ x) i
elim isSetB f op e assc idˡ idʳ (ε-identityʳ x i) = idʳ (elim isSetB f op e assc idˡ idʳ x) i
elim isSetB f op e assc idˡ idʳ (squash x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 isSetB
    (elim isSetB f op e assc idˡ idʳ x) (elim isSetB f op e assc idˡ idʳ y)
    (cong (elim isSetB f op e assc idˡ idʳ) p) (cong (elim isSetB f op e assc idˡ idʳ) q) (squash x y p q) i j


------------------------------------------------------------------------
-- The simplified free monoid type

-- Defined in Cubical.Data.List
open import Cubical.Data.List
open Structures isSetA public


------------------------------------------------------------------------
-- Proving the two types are equivalent

List→FreeM : List A → FreeM
List→FreeM []       = ε
List→FreeM (x ∷ xs) = inj x • List→FreeM xs

FreeM→List : FreeM → List A
FreeM→List = elim (λ _ → isOfHLevelList 0 isSetA) [_] _++_ [] ++-assoc ++-identityˡ ++-identityʳ

++-hom : Homomorphic₂ List→FreeM _++_ _•_
++-hom [] ys = sym (ε-identityˡ _)
++-hom (x ∷ xs) ys = cong (inj x •_) (++-hom xs ys) ∙ sym (•-assoc (inj x) (List→FreeM xs) (List→FreeM ys))

List→FreeM→List : retract List→FreeM FreeM→List
List→FreeM→List [] = refl
List→FreeM→List (x ∷ xs) = cong (x ∷_) (List→FreeM→List xs)

FreeM→List→FreeM : section List→FreeM FreeM→List
FreeM→List→FreeM = elim (λ _ → isSet→isGroupoid squash _ _) (λ _ → ε-identityʳ _) sectionOp refl
                    (λ _ _ _ → isOfHLevelPathP' 0 (squash _ _) _ _ .fst)
                    (λ _ → isOfHLevelPathP' 0 (squash _ _) _ _ .fst)
                    (λ _ → isOfHLevelPathP' 0 (squash _ _) _ _ .fst)
  where
    sectionOp : ∀ {x y} → List→FreeM (FreeM→List x) ≡ x →
                          List→FreeM (FreeM→List y) ≡ y →
                          List→FreeM (FreeM→List (x • y)) ≡ (x • y)
    sectionOp {x} {y} p q =
      List→FreeM (FreeM→List (x • y))                       ≡⟨⟩
      List→FreeM (FreeM→List x ++ FreeM→List y)             ≡⟨ ++-hom (FreeM→List x) (FreeM→List y) ⟩
      List→FreeM (FreeM→List x) • List→FreeM (FreeM→List y) ≡⟨ cong₂ _•_ p q ⟩
      x • y                                                 ∎

List≃FreeM : List A ≃ FreeM
List≃FreeM = isoToEquiv (iso List→FreeM FreeM→List FreeM→List→FreeM List→FreeM→List)

List≡FreeM : List A ≡ FreeM
List≡FreeM = ua List≃FreeM


------------------------------------------------------------------------
-- Monoid structure

FreeM-isMonoid : IsMonoid FreeM _•_ ε
FreeM-isMonoid = record
  { isSemigroup = record
      { isMagma = record { is-set = squash }
      ; assoc   = •-assoc
      }
  ; identity = ε-identity
  }

FreeMonoid : Monoid ℓ
FreeMonoid = record { isMonoid = FreeM-isMonoid }


EquivFreeM : MonoidEquiv ListMonoid FreeMonoid
EquivFreeM = record
  { eq    = List≃FreeM
  ; isHom = record
      { preservesOp = ++-hom
      ; preservesId = refl
      }
  }

FreeMonoid≡ : ListMonoid ≡ FreeMonoid
FreeMonoid≡ = uaMonoid EquivFreeM
