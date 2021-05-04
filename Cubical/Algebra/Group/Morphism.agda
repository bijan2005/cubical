{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Group.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Algebra
open import Cubical.Algebra.Properties

open import Cubical.Relation.Binary.Reasoning.Equality

private
  variable
    g h : Level

-- The following definition of GroupHom and GroupEquiv are level-wise heterogeneous.
-- This allows for example to deduce that G ≡ F from a chain of isomorphisms
-- G ≃ H ≃ F, even if H does not lie in the same level as G and F.

record IsGroupHom (G : Group g) (H : Group h) (f : ⟨ G ⟩ → ⟨ H ⟩) : Type (ℓ-max g h) where
  constructor isgrouphom

  private
    module G = Group G
    module H = Group H

  field
    preservesOp : Homomorphic₂ f G._•_ H._•_

  preservesId : Homomorphic₀ f G.ε H.ε
  preservesId = H.cancelʳ _ (
    f G.ε H.• f G.ε ≡˘⟨ preservesOp G.ε G.ε ⟩
    f (G.ε G.• G.ε) ≡⟨ cong f (G.identityˡ G.ε) ⟩
    f G.ε           ≡˘⟨ H.identityˡ (f G.ε) ⟩
    H.ε H.• f G.ε   ∎)

  preservesInv : Homomorphic₁ f G._⁻¹ H._⁻¹
  preservesInv x = H.inv-uniqueʳ _ _ (
    f (x G.⁻¹) H.• f x ≡˘⟨ preservesOp (x G.⁻¹) x ⟩
    f (x G.⁻¹ G.• x)   ≡⟨ cong f (G.inverseˡ x) ⟩
    f G.ε              ≡⟨ preservesId ⟩
    H.ε                ∎)

record GroupHom (G : Group g) (H : Group h) : Type (ℓ-max g h) where
  constructor grouphom
  field
    fun : ⟨ G ⟩ → ⟨ H ⟩
    isHom : IsGroupHom G H fun

  open IsGroupHom isHom public

record GroupEquiv (G : Group g) (H : Group h) : Type (ℓ-max g h) where
  constructor groupequiv
  field
    eq : ⟨ G ⟩ ≃ ⟨ H ⟩
    isHom : IsGroupHom G H (equivFun eq)

  open IsGroupHom isHom public

  hom : GroupHom G H
  hom = grouphom (equivFun eq) isHom
