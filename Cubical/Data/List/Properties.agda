{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Data.List.Properties where

open import Agda.Builtin.List
open import Cubical.Core.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Prod using (_,_)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary
open import Cubical.Algebra

open import Cubical.Data.List.Base

module _ {ℓ} {A : Type ℓ} where

  private
    _++′_ = _++_ {A = A}

  ++-identityˡ : LeftIdentity [] _++′_
  ++-identityˡ _ = refl

  ++-identityʳ : RightIdentity [] _++′_
  ++-identityʳ [] = refl
  ++-identityʳ (x ∷ xs) = cong (_∷_ x) (++-identityʳ xs)

  ++-identity : Identity [] _++′_
  ++-identity = ++-identityˡ , ++-identityʳ

  ++-assoc : Associative (_++_ {A = A})
  ++-assoc [] ys zs = refl
  ++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

  rev-snoc : (xs : List A) (y : A) → rev (xs ++ [ y ]) ≡ y ∷ rev xs
  rev-snoc [] y = refl
  rev-snoc (x ∷ xs) y = cong (_++ [ x ]) (rev-snoc xs y)

  rev-++ : (xs ys : List A) → rev (xs ++ ys) ≡ rev ys ++ rev xs
  rev-++ [] ys = sym (++-identityʳ (rev ys))
  rev-++ (x ∷ xs) ys =
    cong (λ zs → zs ++ [ x ]) (rev-++ xs ys)
    ∙ ++-assoc (rev ys) (rev xs) [ x ]

  rev-rev : (xs : List A) → rev (rev xs) ≡ xs
  rev-rev [] = refl
  rev-rev (x ∷ xs) = rev-snoc (rev xs) x ∙ cong (_∷_ x) (rev-rev xs)

  rev-rev-snoc : (xs : List A) (y : A) →
    Square (rev-rev (xs ++ [ y ])) (cong (_++ [ y ]) (rev-rev xs)) (cong rev (rev-snoc xs y)) refl
  rev-rev-snoc [] y = sym (lUnit refl)
  rev-rev-snoc (x ∷ xs) y i j =
    hcomp
      (λ k → λ
        { (i = i1) → compPath-filler (rev-snoc (rev xs) x) (cong (x ∷_) (rev-rev xs)) k j ++ [ y ]
        ; (j = i0) → rev (rev-snoc xs y i ++ [ x ])
        ; (j = i1) → x ∷ rev-rev-snoc xs y i k
        })
      (rev-snoc (rev-snoc xs y i) x j)

  data SnocView : List A → Type ℓ where
    nil : SnocView []
    snoc : (x : A) → (xs : List A) → (sx : SnocView xs) → SnocView (xs ∷ʳ x)

  snocView : (xs : List A) → SnocView xs
  snocView xs = helper nil xs
    where
    helper : {l : List A} -> SnocView l -> (r : List A) -> SnocView (l ++ r)
    helper {l} sl [] = subst SnocView (sym (++-identityʳ l)) sl
    helper {l} sl (x ∷ r) = subst SnocView (++-assoc l (x ∷ []) r) (helper (snoc x l sl) r)

-- Path space of list type
module ListPath {ℓ} {A : Type ℓ} where

  Cover : List A → List A → Type ℓ
  Cover [] [] = Lift ⊤
  Cover [] (_ ∷ _) = Lift ⊥
  Cover (_ ∷ _) [] = Lift ⊥
  Cover (x ∷ xs) (y ∷ ys) = (x ≡ y) × Cover xs ys

  reflCode : ∀ xs → Cover xs xs
  reflCode [] = lift tt
  reflCode (_ ∷ xs) = refl , reflCode xs

  encode : ∀ xs ys → (p : xs ≡ ys) → Cover xs ys
  encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

  encodeRefl : ∀ xs → encode xs xs refl ≡ reflCode xs
  encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

  decode : ∀ xs ys → Cover xs ys → xs ≡ ys
  decode [] [] _ = refl
  decode [] (_ ∷ _) (lift ())
  decode (x ∷ xs) [] (lift ())
  decode (x ∷ xs) (y ∷ ys) (p , c) = cong₂ _∷_ p (decode xs ys c)

  decodeRefl : ∀ xs → decode xs xs (reflCode xs) ≡ refl
  decodeRefl [] = refl
  decodeRefl (x ∷ xs) = cong (cong₂ _∷_ refl) (decodeRefl xs)

  decodeEncode : ∀ xs ys → (p : xs ≡ ys) → decode xs ys (encode xs ys p) ≡ p
  decodeEncode xs _ =
    J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
      (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

  isOfHLevelCover : (n : HLevel) (p : isOfHLevel (suc (suc n)) A)
    (xs ys : List A) → isOfHLevel (suc n) (Cover xs ys)
  isOfHLevelCover n p [] [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊤)
  isOfHLevelCover n p [] (y ∷ ys) =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) [] =
    isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
  isOfHLevelCover n p (x ∷ xs) (y ∷ ys) =
    isOfHLevelΣ (suc n) (p x y) (\ _ → isOfHLevelCover n p xs ys)

isOfHLevelList : ∀ {ℓ} (n : HLevel) {A : Type ℓ}
  → isOfHLevel (suc (suc n)) A → isOfHLevel (suc (suc n)) (List A)
isOfHLevelList n ofLevel xs ys =
  isOfHLevelRetract (suc n)
    (ListPath.encode xs ys)
    (ListPath.decode xs ys)
    (ListPath.decodeEncode xs ys)
    (ListPath.isOfHLevelCover n ofLevel xs ys)

private
  variable
    ℓ : Level
    A : Type ℓ

  caseList : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (n c : B) → List A → B
  caseList n _ []      = n
  caseList _ c (_ ∷ _) = c

  safe-head : A → List A → A
  safe-head x []      = x
  safe-head _ (x ∷ _) = x

  safe-tail : List A → List A
  safe-tail []       = []
  safe-tail (_ ∷ xs) = xs

cons-inj₁ : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
cons-inj₁ {x = x} p = cong (safe-head x) p

cons-inj₂ : ∀ {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cons-inj₂ = cong safe-tail

¬cons≡nil : ∀ {x : A} {xs} → ¬ (x ∷ xs ≡ [])
¬cons≡nil {A = A} p = lower (subst (caseList (Lift ⊥) (List A)) p [])

¬nil≡cons : ∀ {x : A} {xs} → ¬ ([] ≡ x ∷ xs)
¬nil≡cons {A = A} p = lower (subst (caseList (List A) (Lift ⊥)) p [])

¬snoc≡nil : ∀ {x : A} {xs} → ¬ (xs ∷ʳ x ≡ [])
¬snoc≡nil {xs = []} contra = ¬cons≡nil contra
¬snoc≡nil {xs = x ∷ xs} contra = ¬cons≡nil contra

¬nil≡snoc : ∀ {x : A} {xs} → ¬ ([] ≡ xs ∷ʳ x)
¬nil≡snoc contra = ¬snoc≡nil (sym contra)

cons≡rev-snoc : (x : A) → (xs : List A) → x ∷ rev xs ≡ rev (xs ∷ʳ x)
cons≡rev-snoc _ [] = refl
cons≡rev-snoc x (y ∷ ys) = λ i → cons≡rev-snoc x ys i ++ y ∷ []

isContr[]≡[] : isContr (Path (List A) [] [])
isContr[]≡[] = refl , ListPath.decodeEncode [] []

isPropXs≡[] : {xs : List A} → isProp (xs ≡ [])
isPropXs≡[] {xs = []} = isOfHLevelSuc 0 isContr[]≡[]
isPropXs≡[] {xs = x ∷ xs} = λ p _ → ⊥.rec (¬cons≡nil p)

discreteList : Discrete A → Discrete (List A)
discreteList eqA []       []       = yes refl
discreteList eqA []       (y ∷ ys) = no ¬nil≡cons
discreteList eqA (x ∷ xs) []       = no ¬cons≡nil
discreteList eqA (x ∷ xs) (y ∷ ys) with eqA x y | discreteList eqA xs ys
... | yes p | yes q = yes (λ i → p i ∷ q i)
... | yes _ | no ¬q = no (λ p → ¬q (cons-inj₂ p))
... | no ¬p | _     = no (λ q → ¬p (cons-inj₁ q))

foldrCons : (xs : List A) → foldr _∷_ [] xs ≡ xs
foldrCons [] = refl
foldrCons (x ∷ xs) = cong (x ∷_) (foldrCons xs)

------------------------------------------------------------------------
-- Structures of List

module Structures {ℓ} {A : Type ℓ} (isSetA : isSet A) where

  List-isMagma : IsMagma (List A) _++_
  List-isMagma = record { is-set = isOfHLevelList 0 isSetA }

  ListMagma : Magma ℓ
  ListMagma = record { isMagma = List-isMagma }


  List-isSemigroup : IsSemigroup (List A) _++_
  List-isSemigroup = record
    { isMagma = List-isMagma
    ; assoc   = ++-assoc
    }

  ListSemigroup : Semigroup ℓ
  ListSemigroup = record { isSemigroup = List-isSemigroup }


  List-isMonoid : IsMonoid (List A) _++_ []
  List-isMonoid = record
    { isSemigroup = List-isSemigroup
    ; identity    = ++-identity
    }

  ListMonoid : Monoid ℓ
  ListMonoid = record { isMonoid = List-isMonoid }
