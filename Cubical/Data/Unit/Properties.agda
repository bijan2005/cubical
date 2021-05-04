{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Unit.Properties where

open import Cubical.Core.Everything

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Unit.Base
open import Cubical.Data.Prod.Base

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

isContr⊤ : isContr ⊤
isContr⊤ = tt , λ {tt → refl}

isProp⊤ : isProp ⊤
isProp⊤ _ _ i = tt -- definitionally equal to: isContr→isProp isContrUnit

isSet⊤ : isSet ⊤
isSet⊤ = isProp→isSet isProp⊤

isOfHLevel⊤ : (n : HLevel) → isOfHLevel n ⊤
isOfHLevel⊤ n = isContr→isOfHLevel n isContr⊤

diagonal-unit : ⊤ ≡ ⊤ × ⊤
diagonal-unit = isoToPath (iso (λ x → tt , tt) (λ x → tt) (λ {(tt , tt) i → tt , tt}) λ {tt i → tt})

fibId : ∀ {ℓ} (A : Type ℓ) → (fiber (λ (x : A) → tt) tt) ≡ A
fibId A = isoToPath
            (iso fst
                 (λ a → a , refl)
                 (λ _ → refl)
                 (λ a i → fst a
                         , isOfHLevelSuc 1 isProp⊤ _ _ (snd a) refl i))
