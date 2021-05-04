{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.Maybe.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Embedding
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary
open import Cubical.Data.Sum
open import Cubical.Relation.Nullary using (Dec; yes; no)

open import Cubical.Data.Maybe.Base

map-Maybe-id : ∀ {ℓ} {A : Type ℓ} → ∀ m → map-Maybe (idfun A) m ≡ m
map-Maybe-id nothing = refl
map-Maybe-id (just _) = refl

-- Path space of Maybe type
module MaybePath {ℓ} {A : Type ℓ} where
  Cover : Maybe A → Maybe A → Type ℓ
  Cover nothing  nothing   = Lift ⊤
  Cover nothing  (just _)  = Lift ⊥
  Cover (just _) nothing   = Lift ⊥
  Cover (just a) (just a') = a ≡ a'

  reflCode : (c : Maybe A) → Cover c c
  reflCode nothing  = lift tt
  reflCode (just b) = refl

  encode : ∀ c c' → c ≡ c' → Cover c c'
  encode c _ = J (λ c' _ → Cover c c') (reflCode c)

  encodeRefl : ∀ c → encode c c refl ≡ reflCode c
  encodeRefl c = JRefl (λ c' _ → Cover c c') (reflCode c)

  decode : ∀ c c' → Cover c c' → c ≡ c'
  decode nothing  nothing  _ = refl
  decode (just _) (just _) p = cong just p

  decodeRefl : ∀ c → decode c c (reflCode c) ≡ refl
  decodeRefl nothing  = refl
  decodeRefl (just _) = refl

  decodeEncode : ∀ c c' → (p : c ≡ c') → decode c c' (encode c c' p) ≡ p
  decodeEncode c _ =
    J (λ c' p → decode c c' (encode c c' p) ≡ p)
      (cong (decode c c) (encodeRefl c) ∙ decodeRefl c)

  encodeDecode : ∀ c c' → (d : Cover c c') → encode c c' (decode c c' d) ≡ d
  encodeDecode nothing nothing _ = refl
  encodeDecode (just a) (just a') =
    J (λ a' p → encode (just a) (just a') (cong just p) ≡ p) (encodeRefl (just a))

  Cover≃Path : ∀ c c' → Cover c c' ≃ (c ≡ c')
  Cover≃Path c c' = isoToEquiv
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  Cover≡Path : ∀ c c' → Cover c c' ≡ (c ≡ c')
  Cover≡Path c c' = isoToPath
    (iso (decode c c') (encode c c') (decodeEncode c c') (encodeDecode c c'))

  isOfHLevelCover : (n : HLevel)
    → isOfHLevel (suc (suc n)) A
    → ∀ c c' → isOfHLevel (suc n) (Cover c c')
  isOfHLevelCover n p nothing  nothing   = isOfHLevelLift (suc n) (isOfHLevel⊤ (suc n))
  isOfHLevelCover n p nothing  (just a') = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) nothing   = isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (just a) (just a') = p a a'

isOfHLevelMaybe : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A
  → isOfHLevel (suc (suc n)) (Maybe A)
isOfHLevelMaybe n lA c c' =
  isOfHLevelRetract (suc n)
    (MaybePath.encode c c')
    (MaybePath.decode c c')
    (MaybePath.decodeEncode c c')
    (MaybePath.isOfHLevelCover n lA c c')

private
 variable
   ℓ : Level
   A : Type ℓ

fromJust-def : A → Maybe A → A
fromJust-def a nothing = a
fromJust-def _ (just a) = a

Dec→Maybe : Dec A → Maybe A
Dec→Maybe (yes x) = just x
Dec→Maybe (no _) = nothing

just-inj : (x y : A) → just x ≡ just y → x ≡ y
just-inj x _ eq = cong (fromJust-def x) eq

isEmbedding-just : isEmbedding (just {A = A})
isEmbedding-just  w z = MaybePath.Cover≃Path (just w) (just z) .snd

¬nothing≡just : ∀ {x : A} → ¬ (nothing ≡ just x)
¬nothing≡just {A = A} {x = x} p = lower (subst (caseMaybe (Maybe A) (Lift ⊥)) p (just x))

¬just≡nothing : ∀ {x : A} → ¬ (just x ≡ nothing)
¬just≡nothing {A = A} {x = x} p = lower (subst (caseMaybe (Lift ⊥) (Maybe A)) p (just x))

isProp-x≡nothing : (x : Maybe A) → isProp (x ≡ nothing)
isProp-x≡nothing nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isProp⊤) x w
isProp-x≡nothing (just _) p _ = ⊥.rec (¬just≡nothing p)

isProp-nothing≡x : (x : Maybe A) → isProp (nothing ≡ x)
isProp-nothing≡x nothing x w =
  subst isProp (MaybePath.Cover≡Path nothing nothing) (isOfHLevelLift 1 isProp⊤) x w
isProp-nothing≡x (just _) p _ = ⊥.rec (¬nothing≡just p)

isContr-nothing≡nothing : isContr (nothing {A = A} ≡ nothing)
isContr-nothing≡nothing = inhProp→isContr refl (isProp-x≡nothing _)

discreteMaybe : Discrete A → Discrete (Maybe A)
discreteMaybe eqA nothing nothing    = yes refl
discreteMaybe eqA nothing (just a')  = no ¬nothing≡just
discreteMaybe eqA (just a) nothing   = no ¬just≡nothing
discreteMaybe eqA (just a) (just a') with eqA a a'
... | yes p = yes (cong just p)
... | no ¬p = no (λ p → ¬p (just-inj _ _ p))

module Sum⊤ where
  Maybe→Sum⊤ : Maybe A → ⊤ ⊎ A
  Maybe→Sum⊤ nothing  = inl tt
  Maybe→Sum⊤ (just a) = inr a

  Sum⊤→Maybe : ⊤ ⊎ A → Maybe A
  Sum⊤→Maybe (inl _) = nothing
  Sum⊤→Maybe (inr a) = just a

  Maybe→Sum⊤→Maybe : (x : Maybe A) → Sum⊤→Maybe (Maybe→Sum⊤ x) ≡ x
  Maybe→Sum⊤→Maybe nothing  = refl
  Maybe→Sum⊤→Maybe (just _) = refl

  Sum⊤→Maybe→Sum⊤ : (x : ⊤ ⊎ A) → Maybe→Sum⊤ (Sum⊤→Maybe x) ≡ x
  Sum⊤→Maybe→Sum⊤ (inl _) = refl
  Sum⊤→Maybe→Sum⊤ (inr _) = refl

Maybe≡Sum⊤ : Maybe A ≡ ⊤ ⊎ A
Maybe≡Sum⊤ = isoToPath (iso Sum⊤.Maybe→Sum⊤ Sum⊤.Sum⊤→Maybe Sum⊤.Sum⊤→Maybe→Sum⊤ Sum⊤.Maybe→Sum⊤→Maybe)

congMaybeEquiv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → Maybe A ≃ Maybe B
congMaybeEquiv e = isoToEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = map-Maybe (equivFun e)
  isom .inv = map-Maybe (invEq e)
  isom .rightInv nothing = refl
  isom .rightInv (just b) = cong just (retEq e b)
  isom .leftInv nothing = refl
  isom .leftInv (just a) = cong just (secEq e a)
