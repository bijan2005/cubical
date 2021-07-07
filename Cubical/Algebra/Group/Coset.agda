{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Algebra.Group

module Cubical.Algebra.Group.Coset {ℓ} (G : Group ℓ) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (id; _∘_; flip)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Embedding

open import Cubical.Algebra.Group.Subgroup

open import Cubical.Relation.Unary
open import Cubical.Relation.Unary.Properties
open import Cubical.Relation.Binary using (Reflexive; Symmetric; Transitive)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Relation.Binary.Reasoning.Equality

open Group G
open GroupLemmas G

private
  variable
    ℓ′ : Level


_≅[_]ˡ_ : ⟨ G ⟩ → Subgroup G ℓ′ → ⟨ G ⟩ → hProp _
x ≅[ H ]ˡ y = Subgroup.Member H (x ⁻¹ • y)

module _ (H : Subgroup G ℓ′) where
  private module H = Subgroup H

  ≅ˡ-reflexive : Reflexive _≅[ H ]ˡ_
  ≅ˡ-reflexive = subst⁻ (_∈ H.Member) (inverseˡ _) H.preservesId

  ≅ˡ-symmetric : Symmetric _≅[ H ]ˡ_
  ≅ˡ-symmetric {x} {y} = subst (_∈ H.Member) (invDistr (x ⁻¹) y ∙ cong (y ⁻¹ •_) (invInvo x)) ∘ H.preservesInv

  ≅ˡ-transitive : Transitive _≅[ H ]ˡ_
  ≅ˡ-transitive {i} {j} {k} x y = subst (_∈ H.Member) eq (H.preservesOp x y)
    where
      eq : _
      eq =
        (i ⁻¹ • j) • (j ⁻¹ • k) ≡˘⟨ assoc _ _ _ ⟩
        ((i ⁻¹ • j) • j ⁻¹) • k ≡⟨ cong (_• k) (assoc _ _ _) ⟩
        (i ⁻¹ • (j • j ⁻¹)) • k ≡⟨ cong (λ v → (i ⁻¹ • v) • k) (inverseʳ j) ⟩
        (i ⁻¹ • ε) • k          ≡⟨ cong (_• k) (identityʳ (i ⁻¹)) ⟩
        i ⁻¹ • k                ∎


infix 9 _<•_
infixr 9 _<•′_

_<•′_ : ⟨ G ⟩ → Pred ⟨ G ⟩ ℓ′ → Pred ⟨ G ⟩ _
g <•′ H = (g •_) ⊣ H

_<•_ : ⟨ G ⟩ → Subgroup G ℓ′ → Pred ⟨ G ⟩ _
g <• H = g <•′ Subgroup.Member H

module _ (H : Pred ⟨ G ⟩ ℓ′) where

  cosetˡ-identity→ : ε <•′ H ⊆ H
  cosetˡ-identity→ = rec (isProp[ H ] _)
      λ ((h , subh) , εh≡x) → subst (_∈ H) (sym (identityˡ h) ∙ εh≡x) subh

  cosetˡ-identity← : H ⊆ ε <•′ H
  cosetˡ-identity← x∈H = ∣ (_ , x∈H) , identityˡ _ ∣

  cosetˡ-identity : ε <•′ H ⇔ H
  cosetˡ-identity = cosetˡ-identity→ , cosetˡ-identity←


  cosetˡ-assoc→ : ∀ a b → (a • b) <•′ H ⊆ a <•′ b <•′ H
  cosetˡ-assoc→ a b =
    map λ ((h , subh) , abh≡x) → (b • h ,
            ∣ (h , subh) , refl ∣) ,
          sym (assoc _ _ _) ∙ abh≡x

  cosetˡ-assoc← : ∀ a b → a <•′ b <•′ H ⊆ (a • b) <•′ H
  cosetˡ-assoc← a b {x} =
    rec squash λ ((h , subh) , ah≡x) →
      map (λ ((g , subg) , bg≡h) → (g , subg) , (
            a • b • g   ≡⟨ assoc a b g ⟩
            a • (b • g) ≡⟨ cong (a •_) bg≡h ⟩
            a • h       ≡⟨ ah≡x ⟩
            x           ∎
          )) subh

  cosetˡ-assoc : ∀ a b → (a • b) <•′ H ≡ a <•′ b <•′ H
  cosetˡ-assoc a b = ⇔toPath _ _ (cosetˡ-assoc→ a b , cosetˡ-assoc← a b)


module _ (H : Subgroup G ℓ′) where
  private module H = Subgroup H

  g∈gH : ∀ g → g ∈ g <• H
  g∈gH g = ∣ H.ε , identityʳ _ ∣


  ≅-cosetˡ→ : ∀ x y → ⟨ x ≅[ H ]ˡ y ⟩ → x <• H ⇔ y <• H
  ≅-cosetˡ→ x y x≅y = xH⊆yH , xH⊇yH
    where
      xH⊆yH : x <• H ⊆ y <• H
      xH⊆yH {a} = map λ ((h , subh) , xh≡a) → (y ⁻¹ • x • h , H.preservesOp (≅ˡ-symmetric H x≅y) subh) ,
                                                (
                                                  y • (y ⁻¹ • x • h) ≡˘⟨ assoc y (y ⁻¹ • x) h ⟩
                                                  y • (y ⁻¹ • x) • h ≡˘⟨ cong (_• h) (assoc y (y ⁻¹) x) ⟩
                                                  y • y ⁻¹ • x • h   ≡⟨ cong (λ v → v • x • h) (inverseʳ y) ⟩
                                                  ε • x • h          ≡⟨ cong (_• h) (identityˡ x) ⟩
                                                  x • h              ≡⟨ xh≡a ⟩
                                                  a                  ∎)

      xH⊇yH : x <• H ⊇ y <• H
      xH⊇yH {a} = map λ ((h , subh) , yh≡a) → (x ⁻¹ • y • h , H.preservesOp x≅y subh) ,
                                                (
                                                  x • (x ⁻¹ • y • h) ≡˘⟨ assoc x (x ⁻¹ • y) h ⟩
                                                  x • (x ⁻¹ • y) • h ≡˘⟨ cong (_• h) (assoc x (x ⁻¹) y) ⟩
                                                  x • x ⁻¹ • y • h   ≡⟨ cong (λ v → v • y • h) (inverseʳ x) ⟩
                                                  ε • y • h          ≡⟨ cong (_• h) (identityˡ y) ⟩
                                                  y • h              ≡⟨ yh≡a ⟩
                                                  a                  ∎)

  ≅-cosetˡ← : ∀ x y → x <• H ⇔ y <• H → ⟨ x ≅[ H ]ˡ y ⟩
  ≅-cosetˡ← x y (xH⊆yH , yH⊆xH) = rec ((_ ≅[ H ]ˡ _) .snd)
      (λ ((h , subh) , yh≡x) →
        subst (_∈ H.Member) (cong _⁻¹ (
            h              ≡˘⟨ identityˡ h ⟩
            ε • h          ≡˘⟨ cong (_• h) (inverseˡ y) ⟩
            y ⁻¹ • y • h   ≡⟨ assoc _ _ _ ⟩
            y ⁻¹ • (y • h) ≡⟨ cong (y ⁻¹ •_) yh≡x ⟩
            y ⁻¹ • x       ∎
        ) ∙ invDistr (y ⁻¹) x ∙ cong (x ⁻¹ •_) (invInvo y)) (H.preservesInv subh)
      )
      (xH⊆yH {x} (g∈gH x))

  ≅-cosetˡ : ∀ x y → ⟨ x ≅[ H ]ˡ y ⟩ ≃ (x <• H ⇔ y <• H)
  ≅-cosetˡ x y = isPropEquiv→Equiv ((x ≅[ H ]ˡ y) .snd) (isProp⇔ (x <• H) (y <• H))
                                    (≅-cosetˡ→ x y) (≅-cosetˡ← x y)


  cosetˡ-idem→ : ((h , _) : ⟨ H ⟩) → h <• H ⊆ H.Member
  cosetˡ-idem→ (h , subh) = rec (isProp[ H.Member ] _)
    λ ((g , subg) , hg≡x) → subst (_∈ H.Member) hg≡x (H.preservesOp subh subg)

  cosetˡ-idem← : ((h , _) : ⟨ H ⟩) → H.Member ⊆ h <• H
  cosetˡ-idem← (h , subh) {x} subx =
    ∣
      (h ⁻¹ • x , H.preservesOp (H.preservesInv subh) subx) , (
        h • (h ⁻¹ • x) ≡˘⟨ assoc h (h ⁻¹) x ⟩
        (h • h ⁻¹) • x ≡⟨ cong (_• x) (inverseʳ h) ⟩
        ε • x          ≡⟨ identityˡ x ⟩
        x              ∎)
    ∣

  cosetˡ-idem : ((h , _) : ⟨ H ⟩) → h <• H ⇔ H.Member
  cosetˡ-idem h = cosetˡ-idem→ h , cosetˡ-idem← h


_≅[_]ʳ_ : ⟨ G ⟩ → Subgroup G ℓ′ → ⟨ G ⟩ → hProp _
x ≅[ H ]ʳ y = Subgroup.Member H (x • y ⁻¹)

module _ (H : Subgroup G ℓ′) where
  private module H = Subgroup H

  ≅ʳ-reflexive : Reflexive _≅[ H ]ʳ_
  ≅ʳ-reflexive = subst⁻ (_∈ H.Member) (inverseʳ _) H.preservesId

  ≅ʳ-symmetric : Symmetric _≅[ H ]ʳ_
  ≅ʳ-symmetric {x} {y} = subst (_∈ H.Member) (invDistr x (y ⁻¹) ∙ cong (_• x ⁻¹) (invInvo y)) ∘ H.preservesInv

  ≅ʳ-transitive : Transitive _≅[ H ]ʳ_
  ≅ʳ-transitive {i} {j} {k} x y = subst (_∈ H.Member) eq (H.preservesOp x y)
    where
      eq : _
      eq =
        (i • j ⁻¹) • (j • k ⁻¹) ≡˘⟨ assoc _ _ _ ⟩
        ((i • j ⁻¹) • j) • k ⁻¹ ≡⟨ cong (_• k ⁻¹) (assoc _ _ _) ⟩
        (i • (j ⁻¹ • j)) • k ⁻¹ ≡⟨ cong (λ v → (i • v) • k ⁻¹) (inverseˡ j) ⟩
        (i • ε) • k ⁻¹          ≡⟨ cong (_• k ⁻¹) (identityʳ i) ⟩
        i • k ⁻¹                ∎



infix 9 _•>_
infixl 9 _•>′_

_•>′_ : Pred ⟨ G ⟩ ℓ′ → ⟨ G ⟩ → Pred ⟨ G ⟩ _
H •>′ g = (_• g) ⊣ H

_•>_ : Subgroup G ℓ′ → ⟨ G ⟩ → Pred ⟨ G ⟩ _
H •> g = Subgroup.Member H •>′ g


module _ (H : Pred ⟨ G ⟩ ℓ′) where

  cosetʳ-identity→ : H •>′ ε ⊆ H
  cosetʳ-identity→ = rec (isProp[ H ] _)
      λ ((h , subh) , hε≡x) → subst (_∈ H) (sym (identityʳ h) ∙ hε≡x) subh

  cosetʳ-identity← : H ⊆ H •>′ ε
  cosetʳ-identity← x∈H = ∣ (_ , x∈H) , identityʳ _ ∣

  cosetʳ-identity : H •>′ ε ⇔ H
  cosetʳ-identity = cosetʳ-identity→ , cosetʳ-identity←


  cosetʳ-assoc→ : ∀ a b → H •>′ (a • b) ⊆ H •>′ a •>′ b
  cosetʳ-assoc→ a b =
    map λ ((h , subh) , hab≡x) → (h • a ,
            ∣ (h , subh) , refl ∣) ,
          assoc _ _ _ ∙ hab≡x

  cosetʳ-assoc← : ∀ a b → H •>′ a •>′ b ⊆ H •>′ (a • b)
  cosetʳ-assoc← a b {x} =
    rec squash λ ((h , subh) , hb≡x) →
      map (λ ((g , subg) , ga≡h) → (g , subg) , (
            g • (a • b) ≡˘⟨ assoc g a b ⟩
            (g • a) • b ≡⟨ cong (_• b) ga≡h ⟩
            h • b       ≡⟨ hb≡x ⟩
            x           ∎
          )) subh

  cosetʳ-assoc : ∀ a b → H •>′ (a • b) ≡ H •>′ a •>′ b
  cosetʳ-assoc a b = ⇔toPath _ _ (cosetʳ-assoc→ a b , cosetʳ-assoc← a b)


module _ (H : Subgroup G ℓ′) where
  private module H = Subgroup H

  g∈Hg : ∀ g → g ∈ H •> g
  g∈Hg g = ∣ H.ε , identityˡ _ ∣


  ≅-cosetʳ→ : ∀ x y → ⟨ x ≅[ H ]ʳ y ⟩ → H •> x ⇔ H •> y
  ≅-cosetʳ→ x y x≅y = Hx⊆Hy , Hx⊇Hy
    where
      Hx⊆Hy : H •> x ⊆ H •> y
      Hx⊆Hy {a} = map
        λ ((h , subh) , hx≡a) → (h • (x • y ⁻¹) , H.preservesOp subh x≅y) , (
                                  h • (x • y ⁻¹) • y   ≡˘⟨ cong (_• y) (assoc h x (y ⁻¹)) ⟩
                                  h • x • y ⁻¹ • y     ≡⟨ assoc (h • x) (y ⁻¹) y ⟩
                                  (h • x) • (y ⁻¹ • y) ≡⟨ cong (h • x •_) (inverseˡ y) ⟩
                                  h • x • ε            ≡⟨ identityʳ (h • x) ⟩
                                  h • x                ≡⟨ hx≡a ⟩
                                  a                    ∎)

      Hx⊇Hy : H •> x ⊇ H •> y
      Hx⊇Hy {a} = map
        λ ((h , subh) , hy≡a) → (h • (y • x ⁻¹) , H.preservesOp subh (≅ʳ-symmetric H x≅y)) , (
                                  h • (y • x ⁻¹) • x   ≡˘⟨ cong (_• x) (assoc h y (x ⁻¹)) ⟩
                                  h • y • x ⁻¹ • x     ≡⟨ assoc (h • y) (x ⁻¹) x ⟩
                                  (h • y) • (x ⁻¹ • x) ≡⟨ cong (h • y •_) (inverseˡ x) ⟩
                                  h • y • ε            ≡⟨ identityʳ (h • y) ⟩
                                  h • y                ≡⟨ hy≡a ⟩
                                  a                    ∎)

  ≅-cosetʳ← : ∀ x y → H •> x ⇔ H •> y → ⟨ x ≅[ H ]ʳ y ⟩
  ≅-cosetʳ← x y (Hx⊆Hy , Hy⊆Hx) = rec ((_ ≅[ H ]ʳ _) .snd)
      (λ ((h , subh) , hy≡x) →
        subst (_∈ H.Member) (
          h              ≡˘⟨ identityʳ h ⟩
          h • ε          ≡˘⟨ cong (h •_) (inverseʳ y) ⟩
          h • (y • y ⁻¹) ≡˘⟨ assoc h y (y ⁻¹) ⟩
          (h • y) • y ⁻¹ ≡⟨ cong (_• y ⁻¹) hy≡x ⟩
          x • y ⁻¹       ∎
        ) subh
      )
      (Hx⊆Hy {x} (g∈Hg x))

  ≅-cosetʳ : ∀ x y → ⟨ x ≅[ H ]ʳ y ⟩ ≃ (H •> x ⇔ H •> y)
  ≅-cosetʳ x y = isPropEquiv→Equiv ((x ≅[ H ]ʳ y) .snd) (isProp⇔ (H •> x) (H •> y))
                                    (≅-cosetʳ→ x y) (≅-cosetʳ← x y)


  cosetʳ-idem→ : ((h , _) : ⟨ H ⟩) → H •> h ⊆ H.Member
  cosetʳ-idem→ (h , subh) = rec (isProp[ H.Member ] _)
    λ ((g , subg) , gh≡x) → subst (_∈ H.Member) gh≡x (H.preservesOp subg subh)

  cosetʳ-idem← : ((h , _) : ⟨ H ⟩) → H.Member ⊆ H •> h
  cosetʳ-idem← (h , subh) {x} subx =
    ∣
      (x • h ⁻¹ , H.preservesOp subx (H.preservesInv subh)) , (
        (x • h ⁻¹) • h ≡⟨ assoc x (h ⁻¹) h ⟩
        x • (h ⁻¹ • h) ≡⟨ cong (x •_) (inverseˡ h) ⟩
        x • ε          ≡⟨ identityʳ x ⟩
        x              ∎)
    ∣

  cosetʳ-idem : ((h , _) : ⟨ H ⟩) → H •> h ⇔ H.Member
  cosetʳ-idem h = cosetʳ-idem→ h , cosetʳ-idem← h
