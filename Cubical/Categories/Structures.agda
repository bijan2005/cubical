{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Cubical.Categories.Structures where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels using (isSetΣ)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category

_∋_ : ∀ {ℓ} → (A : Type ℓ) → A → A
_∋_ A x = x

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    𝒞 : Precategory ℓ ℓ'

record StructureOver (𝒞 : Precategory ℓ ℓ') ℓ'' ℓ''' : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))) where
  field
    Struct : 𝒞 .ob → Type ℓ''
    IsHomo : ∀ {x y} → Struct x → Struct y → 𝒞 .hom x y → Type ℓ'''
    isPropIsHomo : ∀ {x y α β f} → isProp (IsHomo {x} {y} α β f)

    idnIsHomo : ∀ {x} (α : Struct x) → IsHomo α α (𝒞 .idn x)
    homoSeq : ∀ {x y z α β γ} {f : 𝒞 .hom x y} {g : 𝒞 .hom y z} →
                IsHomo α β f → IsHomo β γ g → IsHomo α γ (𝒞 .seq f g)

  _⊆_ : ∀ {x} → Struct x → Struct x → Type ℓ'''
  _⊆_ {x} α β = IsHomo α β (𝒞 .idn x)

open StructureOver public renaming (_⊆_ to _[_⊆_])

record StrIsUnivalent {𝒞 : Precategory ℓ ℓ'} (S : StructureOver 𝒞 ℓ'' ℓ''') : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓ'''))) where
  field
    subAntisym : ∀ {x} {α β : S .Struct x} → S [ α ⊆ β ] → S [ β ⊆ α ] → α ≡ β

open StrIsUnivalent public

isPropP : {A : I → Type ℓ} {x : A i0} {y : A i1} → isProp (A i1) → PathP A x y
isPropP Aprop = toPathP (Aprop _ _)

STRUCTURES : (𝒞 : Precategory ℓ ℓ') → StructureOver 𝒞 ℓ'' ℓ''' → Precategory (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ''')
STRUCTURES 𝒞 S .ob = Σ (𝒞 .ob) (S .Struct)
STRUCTURES 𝒞 S .hom (x , α) (y , β) = Σ (𝒞 .hom x y) (S .IsHomo α β)
STRUCTURES 𝒞 S .idn (x , α) = 𝒞 .idn x , S .idnIsHomo α
STRUCTURES 𝒞 S .seq (f , hᶠ) (g , hᵍ) = 𝒞 .seq f g , S .homoSeq hᶠ hᵍ
STRUCTURES 𝒞 S .seq-λ (f , hᶠ) = cong₂ _,_ (𝒞 .seq-λ f) (toPathP (S .isPropIsHomo _ _))
STRUCTURES 𝒞 S .seq-ρ (f , hᶠ) = cong₂ _,_ (𝒞 .seq-ρ f) (toPathP (S .isPropIsHomo _ _))
STRUCTURES 𝒞 S .seq-α (f , hᶠ) (g , hᵍ) (h , hʰ) = cong₂ _,_ (𝒞 .seq-α f g h) (toPathP (S .isPropIsHomo _ _))

STRUCTURESisCat : ⦃ 𝒞-cat : isCategory 𝒞 ⦄ {S : StructureOver 𝒞 ℓ'' ℓ'''} → isCategory (STRUCTURES 𝒞 S)
STRUCTURESisCat {{𝒞-cat}} {S = S} .homIsSet {x = x , α} {y = y , β} = isSetΣ (𝒞-cat .homIsSet) (λ _ → isProp→isSet (S .isPropIsHomo))

SIP : ∀ ⦃ 𝒞-cat : isCategory 𝒞 ⦄ ⦃ 𝒞-univ : isUnivalent 𝒞 ⦄ → (S : StructureOver 𝒞 ℓ'' ℓ''') → ⦃ S-univ : StrIsUnivalent S ⦄ → isUnivalent (STRUCTURES 𝒞 S)
SIP {𝒞 = 𝒞} {{𝒞-cat}} {{𝒞-univ}} S {{S-univ}} .univ (x , α) (y , β) = isoToIsEquiv (iso (pathToIso (x , α) (y , β)) catisoToPath sect ret)
  where
    catisoToPath : ∀ {x y : 𝒞 .ob} {α : S .Struct x} {β : S .Struct y} → CatIso (STRUCTURES 𝒞 S) (x , α) (y , β) → (x , α) ≡ (y , β)
    catisoToPath {x = x} {y} {α} {β} (catiso (f , hᶠ) (g , hᵍ) sec ret) = ΣPathTransport→PathΣ _ _ (x≡y , α≡β x≡y α β (subst (S .IsHomo α β) f≡h hᶠ) (subst (S .IsHomo β α) g≡h⁻¹ hᵍ))
      where
        x≅y : CatIso 𝒞 x y
        x≅y = catiso f g (cong fst sec) (cong fst ret)

        x≡y : x ≡ y
        x≡y = uva 𝒞-univ x≅y

        f≡h : f ≡ pathMor 𝒞 x≡y
        f≡h = sym (uvaPathMor 𝒞-univ x≅y)

        g≡h⁻¹ : g ≡ pathMor⁻ 𝒞 x≡y
        g≡h⁻¹ = sym (uvaPathMor⁻ 𝒞-univ x≅y)

        α≡β : ∀ {x y : 𝒞 .ob} (p : x ≡ y)
                (α : S .Struct x) (β : S .Struct y)
                (h⇒ : S .IsHomo α β (pathMor 𝒞 p)) (h⇐ : S .IsHomo β α (pathMor⁻ 𝒞 p))
                → subst (S .Struct) p α ≡ β
        α≡β {x} {y} =
          J (λ z q → ∀ (α : S .Struct x) (β : S .Struct z) (h⇒ : S .IsHomo α β (pathMor 𝒞 q)) (h⇐ : S .IsHomo β α (pathMor⁻ 𝒞 q)) → subst (S .Struct) q α ≡ β)
          (λ α β h⇒ h⇐ → transportRefl α ∙ subAntisym S-univ (subst (S .IsHomo α β) (pathMorRefl {𝒞 = 𝒞}) h⇒) (subst (S .IsHomo β α) (pathMor⁻Refl {𝒞 = 𝒞}) h⇐))

    sect : section (pathToIso (x , α) (y , β)) catisoToPath
    sect (catiso h h⁻¹ sec ret) = {!   !}

    ret : retract (pathToIso (x , α) (y , β)) catisoToPath
    ret = J (λ z q → catisoToPath (pathToIso (x , α) z q) ≡ q)
      (subst {y = (pathToIso (x , α) (x , α) refl)} (λ x → catisoToPath x ≡ refl) (sym (JRefl (λ z _ → (x , α) ≅ z) ?)))
