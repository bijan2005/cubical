{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Algebra.Group

module Cubical.Algebra.Group.Kernel {g h} {G : Group g} {H : Group h} (hom : GroupHom G H) where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Embedding
open import Cubical.Relation.Unary

open import Cubical.Relation.Binary.Reasoning.Equality

module G = Group G
module H = Group H

open GroupHom hom renaming (fun to f)


Kernel : Pred ⟨ G ⟩ h
Kernel x = f x ≡ H.ε

isPropKernel : isPropValued Kernel
isPropKernel x = H.is-set (f x) H.ε

Kernelᵖ : PropPred ⟨ G ⟩ h
Kernelᵖ = Kernel , isPropKernel


------------------------------------------------------------------------
-- Properties of the kernel

ker-preservesId : G.ε ∈ Kernel
ker-preservesId = preservesId

ker-preservesOp : G._•_ Preserves₂ Kernel
ker-preservesOp {x} {y} fx≡ε fy≡ε =
  f (x G.• y) ≡⟨ preservesOp x y ⟩
  f x H.• f y ≡⟨ cong₂ H._•_ fx≡ε fy≡ε ⟩
  H.ε H.• H.ε ≡⟨ H.identityʳ H.ε ⟩
  H.ε         ∎

ker-preservesInv : G._⁻¹ Preserves Kernel
ker-preservesInv {x} fx≡ε =
  f (x G.⁻¹) ≡⟨ preservesInv _ ⟩
  f x H.⁻¹   ≡⟨ cong H._⁻¹ fx≡ε ⟩
  H.ε H.⁻¹   ≡⟨ invId H ⟩
  H.ε        ∎

------------------------------------------------------------------------
-- Injectivity of f

ker⊆ε→inj : Kernel ⊆ ｛ G.ε ｝ → ∀ {x y} → f x ≡ f y → x ≡ y
ker⊆ε→inj sub fx≡fy = inv-≡ʳ G (sub (preservesOp+Inv _ _ ∙ ≡-invʳ H fx≡fy))
  where
    preservesOp+Inv : ∀ a b → f (a G.• b G.⁻¹) ≡ f a H.• f b H.⁻¹
    preservesOp+Inv a b = preservesOp a (b G.⁻¹) ∙ cong (f a H.•_) (preservesInv b)

ker⊆ε→emb : Kernel ⊆ ｛ G.ε ｝ → isEmbedding f
ker⊆ε→emb sub = injEmbedding G.is-set H.is-set (ker⊆ε→inj sub)

inj→ker⊆ε : (∀ {x y} → f x ≡ f y → x ≡ y) → Kernel ⊆ ｛ G.ε ｝
inj→ker⊆ε inj fx≡ε = inj (fx≡ε ∙ sym preservesId)

emb→ker⊆ε : isEmbedding f → Kernel ⊆ ｛ G.ε ｝
emb→ker⊆ε emb = inj→ker⊆ε (invIsEq (emb _ _))
