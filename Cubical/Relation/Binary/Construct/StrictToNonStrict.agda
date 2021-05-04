{-# OPTIONS --cubical --no-import-sorts --safe #-}

open import Cubical.Core.Everything
open import Cubical.Relation.Binary

module Cubical.Relation.Binary.Construct.StrictToNonStrict
  {a ℓ} {A : Type a}
  (_<_ : Rel A ℓ)
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Prod
open import Cubical.Data.Sum.Base renaming (rec to ⊎-rec)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) using ()
open import Cubical.Relation.Binary.Properties
open import Cubical.Relation.Nullary

------------------------------------------------------------------------
-- Conversion

-- _<_ can be turned into _≤_ as follows:

_≤_ : Rel A _
x ≤ y = (x < y) ⊎ (x ≡ y)

------------------------------------------------------------------------
-- The converted relations have certain properties
-- (if the original relations have certain other properties)

≤-isPropValued : isSet A → isPropValued _<_ → Irreflexive _<_ → isPropValued _≤_
≤-isPropValued isSetA propv irrefl x y (inl p) (inl q) = cong inl (propv x y p q)
≤-isPropValued isSetA propv irrefl x y (inl p) (inr q) = ⊥-elim (irrefl→tonoteq _<_ irrefl p q)
≤-isPropValued isSetA propv irrefl x y (inr p) (inl q) = ⊥-elim (irrefl→tonoteq _<_ irrefl q p)
≤-isPropValued isSetA propv irrefl x y (inr p) (inr q) = cong inr (isSetA x y p q)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ = inl

≤-fromEq : FromEq _≤_
≤-fromEq = inr

≤-reflexive : Reflexive _≤_
≤-reflexive = fromeq→reflx _≤_ ≤-fromEq

≤-antisym : Transitive _<_ → Irreflexive _<_ → Antisymmetric _≤_
≤-antisym transitive irrefl (inl x<y) (inl y<x) = ⊥-elim (trans∧irr→asym {_<_ = _<_} transitive irrefl x<y y<x)
≤-antisym _ _ _ (inr y≡x) = sym y≡x
≤-antisym _ _ (inr x≡y) _ = x≡y


≤-transitive : Transitive _<_ → Transitive _≤_
≤-transitive <-trans (inl x<y) (inl y<z) = inl $ <-trans x<y y<z
≤-transitive _       (inl x<y) (inr y≡z) = inl $ Respectsʳ≡ _<_ y≡z x<y
≤-transitive _       (inr x≡y) (inl y<z) = inl $ Respectsˡ≡ _<_ (sym x≡y) y<z
≤-transitive _       (inr x≡y) (inr y≡z) = inr $ x≡y ∙ y≡z

<-≤-trans : Transitive _<_ → Trans _<_ _≤_ _<_
<-≤-trans transitive x<y (inl y<z) = transitive x<y y<z
<-≤-trans transitive x<y (inr y≡z) = Respectsʳ≡ _<_ y≡z x<y

≤-<-trans : Transitive _<_ → Trans _≤_ _<_ _<_
≤-<-trans transitive (inl x<y) y<z = transitive x<y y<z
≤-<-trans transitive (inr x≡y) y<z = Respectsˡ≡ _<_ (sym x≡y) y<z

≤-total : Trichotomous _<_ → Total _≤_
≤-total <-tri x y with <-tri x y
... | tri< x<y x≢y x≯y = inl (inl x<y)
... | tri≡ x≮y x≡y x≯y = inl (inr x≡y)
... | tri> x≮y x≢y x>y = inr (inl x>y)

≤-decidable : Discrete A → Decidable _<_ → Decidable _≤_
≤-decidable _≟_ _<?_ x y with x ≟ y
... | yes p = yes (inr p)
... | no ¬p with x <? y
...     | yes q = yes (inl q)
...     | no ¬q = no (⊎-rec ¬q ¬p)

≤-decidable′ : Trichotomous _<_ → Decidable _≤_
≤-decidable′ compare x y with compare x y
... | tri< x<y _   _ = yes (inl x<y)
... | tri≡ _   x≡y _ = yes (inr x≡y)
... | tri> x≮y x≢y _ = no (⊎-rec x≮y x≢y)

------------------------------------------------------------------------
-- Converting structures

isPreorder : Transitive _<_ → IsPreorder _≤_
isPreorder transitive = record
  { reflexive  = ≤-reflexive
  ; transitive = ≤-transitive transitive
  }

isPartialOrder : IsStrictPartialOrder _<_ → IsPartialOrder _≤_
isPartialOrder spo = record
  { isPreorder = isPreorder S.transitive
  ; antisym    = ≤-antisym S.transitive S.irrefl
  }
  where module S = IsStrictPartialOrder spo

isTotalOrder : IsStrictTotalOrder _<_ → IsTotalOrder _≤_
isTotalOrder sto = record
  { isPartialOrder = isPartialOrder S.isStrictPartialOrder
  ; total          = ≤-total S.compare
  }
  where module S = IsStrictTotalOrder sto

isDecTotalOrder : IsStrictTotalOrder _<_ → IsDecTotalOrder _≤_
isDecTotalOrder sto = record
  { isTotalOrder = isTotalOrder sto
  ; _≤?_         = ≤-decidable′ S.compare
  }
  where module S = IsStrictTotalOrder sto
