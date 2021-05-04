{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Empty.Polymorphic where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

import Cubical.Data.Empty as Empty

⊥ : ∀ {ℓ} → Type ℓ
⊥ = Lift Empty.⊥

⊥-elim : ∀ {w ℓ} {Whatever : ⊥ {ℓ} → Type w} → (witness : ⊥ {ℓ}) → Whatever witness
⊥-elim ()

isProp⊥ : ∀ {ℓ} → isProp (⊥ {ℓ})
isProp⊥ ()

isContr⊥→A : ∀ {ℓ ℓ′} {A : Type ℓ′} → isContr (⊥ {ℓ} → A)
fst isContr⊥→A ()
snd isContr⊥→A f i ()
