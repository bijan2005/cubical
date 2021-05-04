{-

Descriptor language for easily defining relational Algebra

-}
{-# OPTIONS --cubical --no-import-sorts --no-exact-split --safe #-}
module Cubical.Algebra.Relational.Macro where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.RelationalStructure
open import Cubical.Data.Sigma

open import Cubical.Algebra.Relational.Constant
open import Cubical.Algebra.Relational.Function
open import Cubical.Algebra.Relational.Maybe
open import Cubical.Algebra.Relational.Parameterized
open import Cubical.Algebra.Relational.Pointed
open import Cubical.Algebra.Relational.Product

open import Cubical.Algebra.Macro
open import Cubical.Algebra.Maybe

data PosRelDesc (??? : Level) : Type?? where
  -- constant structure: X ??? A
  constant : ??? {???'} ??? hSet ???' ??? PosRelDesc ???
  -- pointed structure: X ??? X
  var : PosRelDesc ???
  -- product of Algebra S,T : X ??? (S X ?? T X)
  _,_ : PosRelDesc ???  ??? PosRelDesc ???  ??? PosRelDesc ???
  -- Maybe on a structure S: X ??? Maybe (S X)
  maybe : PosRelDesc ??? ??? PosRelDesc ???

data RelDesc (??? : Level) : Type?? where
  -- constant structure: X ??? A
  constant : ??? {???'} ??? hSet ???' ??? RelDesc ???
  -- pointed structure: X ??? X
  var : RelDesc ???
  -- product of Algebra S,T : X ??? (S X ?? T X)
  _,_ : RelDesc ???  ??? RelDesc ???  ??? RelDesc ???
  -- structure S parameterized by constant A : X ??? (A ??? S X)
  param : ??? {???'} ??? (A : Type ???') ??? RelDesc ???  ??? RelDesc ???
  -- function from positive structure S to T: X ??? (S X ??? T X)
  function+ : PosRelDesc ??? ??? RelDesc ??? ??? RelDesc ???
  -- Maybe on a structure S: X ??? Maybe (S X)
  maybe : RelDesc ??? ??? RelDesc ???

infixr 4 _,_

posRelDesc???TranspDesc : ??? {???} ??? PosRelDesc ??? ??? TranspDesc ???
posRelDesc???TranspDesc (constant A) = constant (A .fst)
posRelDesc???TranspDesc var = var
posRelDesc???TranspDesc (d??? , d???) = posRelDesc???TranspDesc d??? , posRelDesc???TranspDesc d???
posRelDesc???TranspDesc (maybe d) = maybe (posRelDesc???TranspDesc d)

posRelDesc???RelDesc : ??? {???} ??? PosRelDesc ??? ??? RelDesc ???
posRelDesc???RelDesc (constant A) = constant A
posRelDesc???RelDesc var = var
posRelDesc???RelDesc (d??? , d???) = posRelDesc???RelDesc d??? , posRelDesc???RelDesc d???
posRelDesc???RelDesc (maybe d) = maybe (posRelDesc???RelDesc d)

relDesc???Desc : ??? {???} ??? RelDesc ??? ??? Desc ???
relDesc???Desc (constant A) = constant (A .fst)
relDesc???Desc var = var
relDesc???Desc (d??? , d???) = relDesc???Desc d??? , relDesc???Desc d???
relDesc???Desc (param A d) = function+ (constant A) (relDesc???Desc d)
relDesc???Desc (function+ d??? d???) = function+ (posRelDesc???TranspDesc d???) (relDesc???Desc d???)
relDesc???Desc (maybe d) = maybe (relDesc???Desc d)

{- Universe level calculations -}

posRelMacroStrLevel : ??? {???} ??? PosRelDesc ??? ??? Level
posRelMacroStrLevel d = transpMacroLevel (posRelDesc???TranspDesc d)

relMacroStrLevel : ??? {???} ??? RelDesc ??? ??? Level
relMacroStrLevel d = macroStrLevel (relDesc???Desc d)

posRelMacroRelLevel : ??? {???} ??? PosRelDesc ??? ??? Level
posRelMacroRelLevel (constant {???'} A) = ???'
posRelMacroRelLevel {???} var = ???
posRelMacroRelLevel (d??? , d???) = ???-max (posRelMacroRelLevel d???) (posRelMacroRelLevel d???)
posRelMacroRelLevel (maybe d) = posRelMacroRelLevel d

relMacroRelLevel : ??? {???} ??? RelDesc ??? ??? Level
relMacroRelLevel (constant {???'} A) = ???'
relMacroRelLevel {???} var = ???
relMacroRelLevel (d??? , d???) = ???-max (relMacroRelLevel d???) (relMacroRelLevel d???)
relMacroRelLevel (param {???'} A d) = ???-max ???' (relMacroRelLevel d)
relMacroRelLevel (function+ d??? d???) =
  ???-max (posRelMacroStrLevel d???) (???-max (posRelMacroRelLevel d???) (relMacroRelLevel d???))
relMacroRelLevel (maybe d) = relMacroRelLevel d

{- Definition of structure -}

PosRelMacroStructure : ??? {???} (d : PosRelDesc ???) ??? Type ??? ??? Type (posRelMacroStrLevel d)
PosRelMacroStructure d = TranspMacroStructure (posRelDesc???TranspDesc d)

RelMacroStructure : ??? {???} (d : RelDesc ???) ??? Type ??? ??? Type (relMacroStrLevel d)
RelMacroStructure d = MacroStructure (relDesc???Desc d)

{- Notion of structured relation defined by a descriptor -}

PosRelMacroRelStr : ??? {???} (d : PosRelDesc ???) ??? StrRel {???} (PosRelMacroStructure d) (posRelMacroRelLevel d)
PosRelMacroRelStr (constant A) = ConstantRelStr A
PosRelMacroRelStr var = PointedRelStr
PosRelMacroRelStr (d??? , d???) = ProductRelStr (PosRelMacroRelStr d???) (PosRelMacroRelStr d???)
PosRelMacroRelStr (maybe d) = MaybeRelStr (PosRelMacroRelStr d)

RelMacroRelStr : ??? {???} (d : RelDesc ???) ??? StrRel {???} (RelMacroStructure d) (relMacroRelLevel d)
RelMacroRelStr (constant A) = ConstantRelStr A
RelMacroRelStr var = PointedRelStr
RelMacroRelStr (d??? , d???) = ProductRelStr (RelMacroRelStr d???) (RelMacroRelStr d???)
RelMacroRelStr (param A d) = ParamRelStr A (?? _ ??? RelMacroRelStr d)
RelMacroRelStr (function+ d??? d???) =
  FunctionRelStr (PosRelMacroRelStr d???)  (RelMacroRelStr d???)
RelMacroRelStr (maybe d) = MaybeRelStr (RelMacroRelStr d)

{- Proof that structure induced by descriptor is suitable or positive -}

posRelMacroSuitableRel : ??? {???} (d : PosRelDesc ???) ??? SuitableStrRel _ (PosRelMacroRelStr d)
posRelMacroSuitableRel (constant A) = constantSuitableRel A
posRelMacroSuitableRel var = pointedSuitableRel
posRelMacroSuitableRel (d??? , d???) =
  productSuitableRel (posRelMacroSuitableRel d???) (posRelMacroSuitableRel d???)
posRelMacroSuitableRel (maybe d) = maybeSuitableRel (posRelMacroSuitableRel d)

posRelMacroPositiveRel : ??? {???} (d : PosRelDesc ???) ??? PositiveStrRel (posRelMacroSuitableRel d)
posRelMacroPositiveRel (constant A) = constantPositiveRel A
posRelMacroPositiveRel var = pointedPositiveRel
posRelMacroPositiveRel (d??? , d???) =
  productPositiveRel (posRelMacroPositiveRel d???) (posRelMacroPositiveRel d???)
posRelMacroPositiveRel (maybe d) = maybePositiveRel (posRelMacroPositiveRel d)

relMacroSuitableRel : ??? {???} (d : RelDesc ???) ??? SuitableStrRel _ (RelMacroRelStr d)
relMacroSuitableRel (constant A) = constantSuitableRel A
relMacroSuitableRel var = pointedSuitableRel
relMacroSuitableRel (d??? , d???) = productSuitableRel (relMacroSuitableRel d???) (relMacroSuitableRel d???)
relMacroSuitableRel (param A d) = paramSuitableRel A (?? _ ??? relMacroSuitableRel d)
relMacroSuitableRel (function+ d??? d???) =
  functionSuitableRel (posRelMacroSuitableRel d???) (posRelMacroPositiveRel d???) (relMacroSuitableRel d???)
relMacroSuitableRel (maybe d) = maybeSuitableRel (relMacroSuitableRel d)

{- Proof that structured relations and equivalences agree -}

posRelMacroMatchesEquiv : ??? {???} (d : PosRelDesc ???)
  ??? StrRelMatchesEquiv (PosRelMacroRelStr d) (EquivAction???StrEquiv (transpMacroAction (posRelDesc???TranspDesc d)))
posRelMacroMatchesEquiv (constant A) _ _ _ = idEquiv _
posRelMacroMatchesEquiv var _ _ _ = idEquiv _
posRelMacroMatchesEquiv (d??? , d???) =
  productRelMatchesTransp
    (PosRelMacroRelStr d???) (transpMacroAction (posRelDesc???TranspDesc d???))
    (PosRelMacroRelStr d???) (transpMacroAction (posRelDesc???TranspDesc d???))
    (posRelMacroMatchesEquiv d???) (posRelMacroMatchesEquiv d???)
posRelMacroMatchesEquiv (maybe d) =
  maybeRelMatchesTransp
    (PosRelMacroRelStr d) (transpMacroAction (posRelDesc???TranspDesc d))
    (posRelMacroMatchesEquiv d)

relMacroMatchesEquiv : ??? {???} (d : RelDesc ???)
  ??? StrRelMatchesEquiv (RelMacroRelStr d) (MacroEquivStr (relDesc???Desc d))
relMacroMatchesEquiv (constant A) = constantRelMatchesEquiv A
relMacroMatchesEquiv var = pointedRelMatchesEquiv
relMacroMatchesEquiv (d??? , d???) =
  productRelMatchesEquiv
    (RelMacroRelStr d???) (RelMacroRelStr d???)
    (relMacroMatchesEquiv d???) (relMacroMatchesEquiv d???)
relMacroMatchesEquiv (param A d) =
  paramRelMatchesEquiv A (?? _ ??? RelMacroRelStr d) (?? _ ??? relMacroMatchesEquiv d)
relMacroMatchesEquiv (function+ d??? d???) =
  functionRelMatchesEquiv+
    (PosRelMacroRelStr d???) (transpMacroAction (posRelDesc???TranspDesc d???))
    (RelMacroRelStr d???) (MacroEquivStr (relDesc???Desc d???))
    (posRelMacroMatchesEquiv d???) (relMacroMatchesEquiv d???)
relMacroMatchesEquiv (maybe d) =
  maybeRelMatchesEquiv (RelMacroRelStr d) (relMacroMatchesEquiv d)

-- Module for easy importing
module RelMacro ??? (d : RelDesc ???) where
  relation = RelMacroRelStr d
  suitable = relMacroSuitableRel d
  matches = relMacroMatchesEquiv d
  open Macro ??? (relDesc???Desc d) public
