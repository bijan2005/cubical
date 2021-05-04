{-

Constant structure: _ ??? A

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Relational.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

open import Cubical.Algebra.Constant

private
  variable
    ??? ???' : Level

-- Structured relations

module _ (A : hSet ???') where

  ConstantRelStr : StrRel {??? = ???} (ConstantStructure (A .fst)) ???'
  ConstantRelStr _ a??? a??? = a??? ??? a???

  constantSuitableRel : SuitableStrRel {??? = ???} (ConstantStructure (A .fst)) ConstantRelStr
  constantSuitableRel .quo _ _ _ = isContrSingl _
  constantSuitableRel .symmetric _ = sym
  constantSuitableRel .transitive _ _ = _???_
  constantSuitableRel .set _ = A .snd
  constantSuitableRel .prop _ = A .snd

  constantRelMatchesEquiv : StrRelMatchesEquiv {??? = ???} ConstantRelStr (ConstantEquivStr (A .fst))
  constantRelMatchesEquiv _ _ _ = idEquiv _

  constantRelAction : StrRelAction {??? = ???} ConstantRelStr
  constantRelAction .actStr _ a = a
  constantRelAction .actStrId _ = refl
  constantRelAction .actRel _ a a' p = p

  constantPositiveRel : PositiveStrRel {??? = ???} constantSuitableRel
  constantPositiveRel .act = constantRelAction
  constantPositiveRel .reflexive a = refl
  constantPositiveRel .detransitive R R' p = ??? _ , p , refl ???
  constantPositiveRel .quo R = isoToIsEquiv isom
    where
    open Iso
    isom : Iso _ _
    isom .fun = _
    isom .inv = [_]
    isom .rightInv _ = refl
    isom .leftInv = elimProp (?? _ ??? squash/ _ _) (?? a ??? refl)
