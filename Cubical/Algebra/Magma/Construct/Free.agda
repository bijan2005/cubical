{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.HLevels

module Cubical.Algebra.Magma.Construct.Free {ℓ} (Aˢ : hSet ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Magma

open import Cubical.Data.Empty.Polymorphic
open import Cubical.Data.Prod

A = ⟨ Aˢ ⟩
isSetA = Aˢ .snd

------------------------------------------------------------------------
-- The free magma type

data FreeM : Type ℓ where
  inj : A → FreeM
  _•_ : Op₂ FreeM


------------------------------------------------------------------------
-- Proof the free magma is a set

module FreeMPath where
  Cover : FreeM → FreeM → Type ℓ
  Cover (inj x) (inj y) = x ≡ y
  Cover (inj x) (y₁ • y₂) = ⊥
  Cover (x₁ • x₂) (inj y) = ⊥
  Cover (x₁ • x₂) (y₁ • y₂) = Cover x₁ y₁ × Cover x₂ y₂

  isPropCover : ∀ x y → isProp (Cover x y)
  isPropCover (inj x) (inj y) = isSetA x y
  isPropCover (inj x) (y₁ • y₂) = isProp⊥
  isPropCover (x₁ • x₂) (inj y) = isProp⊥
  isPropCover (x₁ • x₂) (y₁ • y₂) = isPropProd (isPropCover x₁ y₁) (isPropCover x₂ y₂)

  reflCover : ∀ x → Cover x x
  reflCover (inj x) = refl
  reflCover (x • y) = reflCover x , reflCover y

  encode : ∀ x y → x ≡ y → Cover x y
  encode x _ = J (λ y _ → Cover x y) (reflCover x)

  encodeRefl : ∀ x → encode x x refl ≡ reflCover x
  encodeRefl x = JRefl (λ y _ → Cover x y) (reflCover x)

  decode : ∀ x y → Cover x y → x ≡ y
  decode (inj x) (inj y) p = cong inj p
  decode (inj x) (y₁ • y₂) ()
  decode (x₁ • x₂) (inj y) ()
  decode (x₁ • x₂) (y₁ • y₂) (p , q) = cong₂ _•_ (decode x₁ y₁ p) (decode x₂ y₂ q)

  decodeRefl : ∀ x → decode x x (reflCover x) ≡ refl
  decodeRefl (inj x) = refl
  decodeRefl (x • y) i j = decodeRefl x i j • decodeRefl y i j

  decodeEncode : ∀ x y → (p : x ≡ y) → decode x y (encode x y p) ≡ p
  decodeEncode x _ =
    J (λ y p → decode x y (encode x y p) ≡ p)
      (cong (decode x x) (encodeRefl x) ? decodeRefl x)

isSetFreeM : isSet FreeM
isSetFreeM x y =
  isOfHLevelRetract 1
    (FreeMPath.encode x y)
    (FreeMPath.decode x y)
    (FreeMPath.decodeEncode x y)
    (FreeMPath.isPropCover x y)


------------------------------------------------------------------------
-- The free magma

FreeM-isMagma : IsMagma FreeM _•_
FreeM-isMagma = record { is-set = isSetFreeM }

FreeMagma : Magma ℓ
FreeMagma = record { isMagma = FreeM-isMagma }
