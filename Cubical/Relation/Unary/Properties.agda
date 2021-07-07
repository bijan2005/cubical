{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Relation.Unary.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function using (id; _∘_)

open import Cubical.Data.Unit
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Unary

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type ℓ

------------------------------------------------------------------------
-- Special sets


Empty∅ : Empty {A = A} ∅
Empty∅ _ ()

UniversalU : Π[ U {A = A} ]
UniversalU _ = tt


∁∅≡U : ∁ ∅ ≡ U {A = A}
∁∅≡U = ⇔toPath _ _ ((λ _ → tt) , λ _ ())

∁U≡∅ : ∁ U ≡ ∅ {A = A}
∁U≡∅ = ⇔toPath _ _ ((λ f → f tt) , λ ())


------------------------------------------------------------------------
-- Propositions

module _ (P : Pred A ℓ₁) (Q : Pred A ℓ₂) where

  isProp⊆ : isProp (P ⊆ Q)
  isProp⊆ = isPropImplicitΠ λ _ → isPropΠ λ _ → isProp[ Q ] _

  isProp⊂ : isProp (P ⊂ Q)
  isProp⊂ = isProp× isProp⊆ (isPropΠ λ _ → isProp⊥)

  isProp⇔ : isProp (P ⇔ Q)
  isProp⇔ = isProp× isProp⊆ (isPropImplicitΠ λ _ → isPropΠ λ _ → isProp[ P ] _)



module _ (P : Pred A ℓ) where

  isPropEmpty : isProp (Empty P)
  isPropEmpty = isPropΠ2 λ _ _ → isProp⊥

  isPropSatisfiable : isProp ∃⟨ P ⟩
  isPropSatisfiable = squash

  isPropUniversal : isProp Π[ P ]
  isPropUniversal = isPropΠ isProp[ P ]


------------------------------------------------------------------------
-- Predicate equivalence


⇔-reflexive : (P : Pred A ℓ) → P ⇔ P
⇔-reflexive P = id , id

⇔-symmetric : (P : Pred A ℓ₁) (Q : Pred A ℓ₂) → P ⇔ Q → Q ⇔ P
⇔-symmetric P Q (x , y) = (y , x)

⇔-transitive : (P : Pred A ℓ₁) (Q : Pred A ℓ₂) (R : Pred A ℓ₃) →
                  P ⇔ Q → Q ⇔ R → P ⇔ R
⇔-transitive P Q R (x , y) (w , z) = w ∘ x , y ∘ z
