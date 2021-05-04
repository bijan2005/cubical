{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Semigroup.Construct.Free {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Empty.Polymorphic
open import Cubical.Data.Prod

open import Cubical.Relation.Binary.Reasoning.Equality

A = ⟨ Aˢ ⟩
isSetA = Aˢ .snd

------------------------------------------------------------------------
-- The direct free semigroup type

data FreeS′ : Type ℓ where
  inj : A → FreeS′
  _•_ : Op₂ FreeS′

  •-assoc : Associative _•_

  squash : isSet FreeS′


elim : ∀ {ℓ′} {B : FreeS′ → Type ℓ′} →
        (∀ x → isSet (B x)) →
        (∀ x → B (inj x)) →
        (op : ∀ x y → B x → B y → B (x • y)) →
        (∀ x y z (a : B x) (b : B y) (c : B z) → PathP (λ i → B (•-assoc x y z i)) (op _ _ (op _ _ a b) c) (op _ _ a (op _ _ b c))) →
        (x : FreeS′) → B x
elim isSetB f op assc (inj x) = f x
elim isSetB f op assc (x • y) = op x y (elim isSetB f op assc x) (elim isSetB f op assc y)
elim isSetB f op assc (•-assoc x y z i) = assc x y z (elim isSetB f op assc x) (elim isSetB f op assc y) (elim isSetB f op assc z) i
elim isSetB f op assc (squash x y p q i j) =
  isOfHLevel→isOfHLevelDep 2 isSetB
    (elim isSetB f op assc x) (elim isSetB f op assc y)
    (cong (elim isSetB f op assc) p) (cong (elim isSetB f op assc) q) (squash x y p q) i j

------------------------------------------------------------------------
-- The simplified free semigroup type

infixl 5 _□
infixr 4 _∶_

data FreeS : Type ℓ where
  _□ : A → FreeS
  _∶_ : A → FreeS → FreeS


module FreeSPath where
  Cover : FreeS → FreeS → Type ℓ
  Cover (x □) (y □) = x ≡ y
  Cover (x □) (y ∶ ys) = ⊥
  Cover (x ∶ xs) (y □) = ⊥
  Cover (x ∶ xs) (y ∶ ys) = (x ≡ y) × Cover xs ys

  isPropCover : ∀ xs ys → isProp (Cover xs ys)
  isPropCover (x □) (y □) = isSetA x y
  isPropCover (x □) (y ∶ ys) = isProp⊥
  isPropCover (x ∶ xs) (y □) = isProp⊥
  isPropCover (x ∶ xs) (y ∶ ys) = isPropProd (isSetA x y) (isPropCover xs ys)

  reflCover : ∀ xs → Cover xs xs
  reflCover (x □)   = refl
  reflCover (x ∶ xs) = refl , reflCover xs

  encode : ∀ xs ys → xs ≡ ys → Cover xs ys
  encode xs _ = J (λ ys _ → Cover xs ys) (reflCover xs)

  encodeRefl : ∀ xs → encode xs xs refl ≡ reflCover xs
  encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCover xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode (x □) (y □) p = cong _□ p
  decode (x □) (y ∶ ys) ()
  decode (x ∶ xs) (y □) ()
  decode (x ∶ xs) (y ∶ ys) (p , q) = cong₂ _∶_ p (decode xs ys q)

  decodeRefl : ∀ xs → decode xs xs (reflCover xs) ≡ refl
  decodeRefl (x □)   = refl
  decodeRefl (x ∶ xs) = cong (cong₂ _∶_ refl) (decodeRefl xs)

  decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs _ =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

isSetFreeS : isSet FreeS
isSetFreeS x y =
  isOfHLevelRetract 1
    (FreeSPath.encode x y)
    (FreeSPath.decode x y)
    (FreeSPath.decodeEncode x y)
    (FreeSPath.isPropCover x y)


_++_ : Op₂ FreeS
(x □) ++ ys = x ∶ ys
(x ∶ xs) ++ ys = x ∶ xs ++ ys

++-assoc : Associative _++_
++-assoc (x □) ys zs = refl
++-assoc (x ∶ xs) ys zs = cong (x ∶_) (++-assoc xs ys zs)


------------------------------------------------------------------------
-- Proving the two types are equivalent

FreeS→FreeS′ : FreeS → FreeS′
FreeS→FreeS′ (x □)   = inj x
FreeS→FreeS′ (x ∶ xs) = inj x • FreeS→FreeS′ xs

FreeS′→FreeS : FreeS′ → FreeS
FreeS′→FreeS = elim (λ _ → isSetFreeS) _□ (λ _ _ → _++_) (λ _ _ _ → ++-assoc)

FreeS→FreeS′→FreeS : retract FreeS→FreeS′ FreeS′→FreeS
FreeS→FreeS′→FreeS (x □) = refl
FreeS→FreeS′→FreeS (x ∶ xs) = cong (x ∶_) (FreeS→FreeS′→FreeS xs)

++-hom : Homomorphic₂ FreeS→FreeS′ _++_ _•_
++-hom (x □)   ys = refl
++-hom (x ∶ xs) ys = cong (inj x •_) (++-hom xs ys) ∙ sym (•-assoc (inj x) (FreeS→FreeS′ xs) (FreeS→FreeS′ ys))

FreeS′→FreeS→FreeS′ : section FreeS→FreeS′ FreeS′→FreeS
FreeS′→FreeS→FreeS′ = elim (λ _ → isSet→isGroupoid squash _ _) (λ _ → refl) sectionOp (λ _ _ _ _ _ _ → isOfHLevelPathP' 0 (squash _ _) _ _ .fst)
  where
    sectionOp : ∀ x y → FreeS→FreeS′ (FreeS′→FreeS x) ≡ x →
                        FreeS→FreeS′ (FreeS′→FreeS y) ≡ y →
                        FreeS→FreeS′ (FreeS′→FreeS (x • y)) ≡ (x • y)
    sectionOp x y p q =
      FreeS→FreeS′ (FreeS′→FreeS (x • y))                           ≡⟨⟩
      FreeS→FreeS′ (FreeS′→FreeS x ++ FreeS′→FreeS y)               ≡⟨ ++-hom (FreeS′→FreeS x) (FreeS′→FreeS y) ⟩
      FreeS→FreeS′ (FreeS′→FreeS x) • FreeS→FreeS′ (FreeS′→FreeS y) ≡⟨ cong₂ _•_ p q ⟩
      x • y                                                         ∎


FreeS≃FreeS′ : FreeS ≃ FreeS′
FreeS≃FreeS′ = isoToEquiv (iso FreeS→FreeS′ FreeS′→FreeS FreeS′→FreeS→FreeS′ FreeS→FreeS′→FreeS)

FreeS≡FreeS′ : FreeS ≡ FreeS′
FreeS≡FreeS′ = ua FreeS≃FreeS′


------------------------------------------------------------------------
-- Semigroup Algebra

FreeS′-isSemigroup : IsSemigroup FreeS′ _•_
FreeS′-isSemigroup = record
  { isMagma = record { is-set = squash }
  ; assoc   = •-assoc
  }

FreeS-isSemigroup : IsSemigroup FreeS _++_
FreeS-isSemigroup = record
  { isMagma = record { is-set = isSetFreeS }
  ; assoc   = ++-assoc
  }


FreeSemigroup′ : Semigroup ℓ
FreeSemigroup′ = record { isSemigroup = FreeS′-isSemigroup }

FreeSemigroup : Semigroup ℓ
FreeSemigroup = record { isSemigroup = FreeS-isSemigroup }


EquivFreeS : SemigroupEquiv FreeSemigroup FreeSemigroup′
EquivFreeS = record
  { eq    = FreeS≃FreeS′
  ; isHom = ++-hom
  }

FreeSemigroup≡ : FreeSemigroup ≡ FreeSemigroup′
FreeSemigroup≡ = uaSemigroup EquivFreeS
