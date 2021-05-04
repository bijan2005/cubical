{-

Pointed structure: X ??? X

-}
{-# OPTIONS --cubical --no-import-sorts --safe #-}
module Cubical.Algebra.Relational.Pointed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Foundations.Univalence
open import Cubical.Relation.ZigZag.Base
open import Cubical.HITs.SetQuotients
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.Pointed

private
  variable
    ??? : Level

-- Structured relations

PointedRelStr : StrRel PointedStructure ???
PointedRelStr R = R

pointedSuitableRel : SuitableStrRel {??? = ???} PointedStructure PointedRelStr
pointedSuitableRel .quo _ _ _ = isContrSingl _
pointedSuitableRel .symmetric _ r = r
pointedSuitableRel .transitive _ _ r r' = ??? _ , r , r' ???
pointedSuitableRel .set setX = setX
pointedSuitableRel .prop propR = propR

pointedRelMatchesEquiv : StrRelMatchesEquiv {??? = ???} PointedRelStr PointedEquivStr
pointedRelMatchesEquiv _ _ _ = idEquiv _

pointedRelAction : StrRelAction {??? = ???} PointedRelStr
pointedRelAction .actStr f = f
pointedRelAction .actStrId _ = refl
pointedRelAction .actRel ?? = ??

pointedPositiveRel : PositiveStrRel {??? = ???} pointedSuitableRel
pointedPositiveRel .act = pointedRelAction
pointedPositiveRel .reflexive x = ??? refl ???
pointedPositiveRel .detransitive R R' rr' = rr'
pointedPositiveRel .quo R = isoToIsEquiv isom
  where
  open Iso
  isom : Iso _ _
  isom .fun = _
  isom .inv q = q
  isom .rightInv = elimProp (?? _ ??? squash/ _ _) (?? _ ??? refl)
  isom .leftInv = elimProp (?? _ ??? squash/ _ _) (?? _ ??? refl)
