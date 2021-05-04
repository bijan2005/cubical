{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Band.Properties where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.NatPlusOne

open import Cubical.Algebra
open import Cubical.Algebra.Properties
open import Cubical.Algebra.Semigroup.Properties using (isPropIsSemigroup)

open import Cubical.Relation.Binary.Reasoning.Equality

private
  variable
    ??? : Level

isPropIsBand : ??? {B : Type ???} {_???_} ??? isProp (IsBand B _???_)
isPropIsBand {_} {_} {_???_} (isband aSemigroup aIdem) (isband bSemigroup bIdem) =
  cong??? isband (isPropIsSemigroup aSemigroup bSemigroup) (isPropIdempotent (IsSemigroup.is-set aSemigroup) _???_ aIdem bIdem)

module BandLemmas (S : Band ???) where
  open Band S

  ^-id : ??? x n ??? x ^ n ??? x
  ^-id x one          = refl
  ^-id x (2+ zero)    = idem x
  ^-id x (2+ (suc n)) =
    x ??? (x ??? x ^ 1+ n) ???????? assoc x x (x ^ 1+ n) ???
    x ??? x ??? x ^ 1+ n   ?????? cong (_??? x ^ 1+ n) (idem x) ???
    x ??? x ^ 1+ n       ?????? ^-id x (2+ n) ???
    x                  ???

open BandLemmas public
