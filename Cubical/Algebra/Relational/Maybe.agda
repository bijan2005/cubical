{-

Maybe structure: X ??? Maybe (S X)

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Algebra.Relational.Maybe where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Maybe
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as Trunc
open import Cubical.HITs.SetQuotients

open import Cubical.Algebra.Maybe

private
  variable
    ??? ?????? ??????' ??????'' : Level

-- Structured relations

MaybeRelStr : {S : Type ??? ??? Type ??????} {??????' : Level}
  ??? StrRel S ??????' ??? StrRel (?? X ??? Maybe (S X)) ??????'
MaybeRelStr ?? R = MaybeRel (?? R)

maybeSuitableRel : {S : Type ??? ??? Type ??????} {?? : StrRel S ??????'}
  ??? SuitableStrRel S ??
  ??? SuitableStrRel (MaybeStructure S) (MaybeRelStr ??)
maybeSuitableRel ?? .quo (X , nothing) R _ .fst = nothing , _
maybeSuitableRel ?? .quo (X , nothing) R _ .snd (nothing , _) = refl
maybeSuitableRel ?? .quo (X , just s) R c .fst =
  just (?? .quo (X , s) R c .fst .fst) , ?? .quo (X , s) R c .fst .snd
maybeSuitableRel ?? .quo (X , just s) R c .snd (just s' , r) =
  cong (?? {(t , r') ??? just t , r'}) (?? .quo (X , s) R c .snd (s' , r))
maybeSuitableRel ?? .symmetric R {nothing} {nothing} r = _
maybeSuitableRel ?? .symmetric R {just s} {just t} r = ?? .symmetric R r
maybeSuitableRel ?? .transitive R R' {nothing} {nothing} {nothing} r r' = _
maybeSuitableRel ?? .transitive R R' {just s} {just t} {just u} r r' = ?? .transitive R R' r r'
maybeSuitableRel ?? .set setX = isOfHLevelMaybe 0 (?? .set setX)
maybeSuitableRel ?? .prop propR nothing nothing = isOfHLevelLift 1 isPropUnit
maybeSuitableRel ?? .prop propR nothing (just y) = isOfHLevelLift 1 isProp???
maybeSuitableRel ?? .prop propR (just x) nothing = isOfHLevelLift 1 isProp???
maybeSuitableRel ?? .prop propR (just x) (just y) = ?? .prop propR x y

maybeRelMatchesEquiv : {S : Type ??? ??? Type ??????} (?? : StrRel S ??????') {?? : StrEquiv S ??????''}
  ??? StrRelMatchesEquiv ?? ??
  ??? StrRelMatchesEquiv (MaybeRelStr ??) (MaybeEquivStr ??)
maybeRelMatchesEquiv ?? ?? (X , nothing) (Y , nothing) _ = Lift???Lift (idEquiv _)
maybeRelMatchesEquiv ?? ?? (X , nothing) (Y , just y) _ = Lift???Lift (idEquiv _)
maybeRelMatchesEquiv ?? ?? (X , just x) (Y , nothing) _ = Lift???Lift (idEquiv _)
maybeRelMatchesEquiv ?? ?? (X , just x) (Y , just y) = ?? (X , x) (Y , y)

maybeRelAction :
  {S : Type ??? ??? Type ??????} {?? : StrRel S ??????'}
  ??? StrRelAction ??
  ??? StrRelAction (MaybeRelStr ??)
maybeRelAction ?? .actStr f = map-Maybe (?? .actStr f)
maybeRelAction ?? .actStrId s =
  funExt??? (cong map-Maybe (funExt (?? .actStrId))) s ??? map-Maybe-id s
maybeRelAction ?? .actRel h nothing nothing = _
maybeRelAction ?? .actRel h (just s) (just t) r = ?? .actRel h s t r

maybePositiveRel :
  {S : Type ??? ??? Type ??????} {?? : StrRel S ??????'} {?? : SuitableStrRel S ??}
  ??? PositiveStrRel ??
  ??? PositiveStrRel (maybeSuitableRel ??)
maybePositiveRel ?? .act = maybeRelAction (?? .act)
maybePositiveRel ?? .reflexive nothing = _
maybePositiveRel ?? .reflexive (just s) = ?? .reflexive s
maybePositiveRel ?? .detransitive R R' {nothing} {nothing} r = ??? nothing , _ , _ ???
maybePositiveRel ?? .detransitive R R' {just s} {just u} rr' =
  Trunc.map (?? {(t , r , r') ??? just t , r , r'}) (?? .detransitive R R' rr')
maybePositiveRel {S = S} {?? = ??} {?? = ??} ?? .quo {X} R =
  subst isEquiv
    (funExt
      (elimProp (?? _ ??? maybeSuitableRel ?? .set squash/ _ _)
        (?? {nothing ??? refl; (just _) ??? refl})))
    (compEquiv (isoToEquiv isom) (congMaybeEquiv (_ , ?? .quo R)) .snd)
  where
  fwd : Maybe (S X) / MaybeRel (?? (R .fst .fst)) ??? Maybe (S X / ?? (R .fst .fst))
  fwd [ nothing ] = nothing
  fwd [ just s ] = just [ s ]
  fwd (eq/ nothing nothing r i) = nothing
  fwd (eq/ (just s) (just t) r i) = just (eq/ s t r i)
  fwd (squash/ _ _ p q i j) =
    isOfHLevelMaybe 0 squash/ _ _ (cong fwd p) (cong fwd q) i j

  bwd : Maybe (S X / ?? (R .fst .fst)) ??? Maybe (S X) / MaybeRel (?? (R .fst .fst))
  bwd nothing = [ nothing ]
  bwd (just [ s ]) = [ just s ]
  bwd (just (eq/ s t r i)) = eq/ (just s) (just t) r i
  bwd (just (squash/ _ _ p q i j)) =
    squash/ _ _ (cong (bwd ??? just) p) (cong (bwd ??? just) q) i j

  open Iso
  isom : Iso (Maybe (S X) / MaybeRel (?? (R .fst .fst))) (Maybe (S X / ?? (R .fst .fst)))
  isom .fun = fwd
  isom .inv = bwd
  isom .rightInv nothing = refl
  isom .rightInv (just x) =
    elimProp {B = ?? x ??? fwd (bwd (just x)) ??? just x}
      (?? _ ??? isOfHLevelMaybe 0 squash/ _ _)
      (?? _ ??? refl)
      x
  isom .leftInv = elimProp (?? _ ??? squash/ _ _) (?? {nothing ??? refl; (just _) ??? refl})

maybeRelMatchesTransp : {S : Type ??? ??? Type ??????}
  (?? : StrRel S ??????') (?? : EquivAction S)
  ??? StrRelMatchesEquiv ?? (EquivAction???StrEquiv ??)
  ??? StrRelMatchesEquiv (MaybeRelStr ??) (EquivAction???StrEquiv (maybeEquivAction ??))
maybeRelMatchesTransp _ _ ?? (X , nothing) (Y , nothing) _ =
  isContr???Equiv (isOfHLevelLift 0 isContrUnit) isContr-nothing???nothing
maybeRelMatchesTransp _ _ ?? (X , nothing) (Y , just y) _ =
  uninhabEquiv lower ??nothing???just
maybeRelMatchesTransp _ _ ?? (X , just x) (Y , nothing) _ =
  uninhabEquiv lower ??just???nothing
maybeRelMatchesTransp _ _ ?? (X , just x) (Y , just y) e =
  compEquiv (?? (X , x) (Y , y) e) (_ , isEmbedding-just _ _)
