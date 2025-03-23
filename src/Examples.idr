-- Each program is repeated twice: once as an intrinsically-typed term, and once
-- as an untyped term. The goal is to show that the type-checker can reconstruct
-- a type which is equivalent to the intrinsic type, up to reordering.
module Examples

import Elem
import Cover
import ITerm
import Ty
import UTerm

----------------------------------------

public export
iconsume
   : (g : List Ty)
  -> {a : Ty}
  -> {d : List Ty}
  -> (aElemG : Elem a g)
  -> IConsumer (allButElem aElemG) a d
  -> ICmd g d
iconsume g {a} {d} aElemG consumer
  = ICut
      a
      g (pickLeftFromElem aElemG)
      d allRight
      (IVar a)
      consumer

public export
uconsume
   : String
  -> UConsumer
  -> UCmd
uconsume x consumer
  = UCut (UVar x) consumer

----------------------------------------

public export
iproduce
   : {g : List Ty}
  -> {a : Ty}
  -> (d : List Ty)
  -> (aElemD : Elem a d)
  -> IProducer g a (allButElem aElemD)
  -> ICmd g d
iproduce {g} {a} d aElemD producer
  = ICut
      a
      g allLeft
      d (pickRightFromElem aElemD)
      producer
      (ICoVar a)

public export
uproduce
   : String
  -> UProducer
  -> UCmd
uproduce x producer
  = UCut producer (UCoVar x)

----------------------------------------

iletVar
   : (a : Ty)
  -> (gg' : List Ty)
  -> Cover g g' gg'
  -> (dd' : List Ty)
  -> Cover d d' dd'
  -> IProducer g a d
  -> ICmd (a :: g') d'
  -> ICmd gg' dd'
iletVar a gg' gCover dd' dCover producer body
  = ICut
      a
      gg' gCover
      dd' dCover
      producer
      (ICoMu a body)

uletVar
   : String
  -> UProducer
  -> UCmd
  -> UCmd
uletVar x producer body
  = UCut producer (UCoMu x body)

----------------------------------------

iletCoVar
   : (a : Ty)
  -> (gg' : List Ty)
  -> Cover g g' gg'
  -> (dd' : List Ty)
  -> Cover d d' dd'
  -> IConsumer g a d
  -> ICmd g' (a :: d')
  -> ICmd gg' dd'
iletCoVar a gg' gCover dd' dCover consumer body
  = ICut
      a
      gg' (flipCover gCover)
      dd' (flipCover dCover)
      (IMu a body)
      consumer

uletCoVar
   : String
  -> UConsumer
  -> UCmd
  -> UCmd
uletCoVar x consumer body
  = UCut (UMu x body) consumer

----------------------------------------

public export
ianihilate
   : {a : Ty}
  -> ICmd [a] [a]
ianihilate {a}
  = ICut
      a
      [a] allLeft
      [a] allRight
      (IVar a)
      (ICoVar a)

public export
uanihilate
   : String
  -> String
  -> UCmd
uanihilate x cox
  = UCut (UVar x) (UCoVar cox)

----------------------------------------

public export
ibringVarToFront
   : (a : Ty)
  -> (g : List Ty)
  -> (aElemG : Elem a g)
  -> {d : List Ty}
  -> ICmd (a :: allButElem aElemG) d
  -> ICmd g d
ibringVarToFront a g aElemG cmd
  = iconsume
      g aElemG
      (ICoMu a cmd)

-- no untyped equivalent since the order of variables is irrelevant

----------------------------------------

public export
ibringCoVarToFront
   : (a : Ty)
  -> {g : List Ty}
  -> (d : List Ty)
  -> (aElemD : Elem a d)
  -> ICmd g (a :: allButElem aElemD)
  -> ICmd g d
ibringCoVarToFront a d aElemD cmd
  = iproduce
      d aElemD
      (IMu a cmd)

-- no untyped equivalent since the order of variables is irrelevant

----------------------------------------

-- localCompletenessOfImp f
--   = \x -> f x
public export
ilocalCompletenessOfImp
   : {a, b : Ty}
  -> ICmd [Imp a b] [Imp a b]
ilocalCompletenessOfImp {a} {b}
  = iproduce
      [Imp a b] Here
      (ILam
        a b
        (iconsume
          [a, Imp a b] (There Here)
          (IApp
            a b
            [a] (PickLeft Nil)
            [b] (PickRight Nil)
            (IVar a)
            (ICoVar b))))

public export
ulocalCompletenessOfImp
   : UCmd
ulocalCompletenessOfImp
  = uproduce "out"
      (ULam "a" "b"
        (uconsume "in"
          (UApp
            (UVar "a")
            (UCoVar "b"))))

----------------------------------------

-- localCompletenessOfTen aTenB
--   = case aTenB of
--       (a, b) -> Pair a b
public export
ilocalCompletenessOfTen
   : {a, b : Ty}
  -> ICmd [Ten a b] [Ten a b]
ilocalCompletenessOfTen {a} {b}
  = iconsume
      [Ten a b] Here
      (IMatchPair
        a b
        (iproduce
          [Ten a b] Here
          (IPair
            a b
            [a, b] (PickLeft $ PickRight Nil)
            [] Nil
            (IVar a)
            (IVar b))))

public export
ulocalCompletenessOfTen
   : UCmd
ulocalCompletenessOfTen
  = uconsume "in"
      (UMatchPair "a" "b"
        (uproduce "out"
          (UPair
            (UVar "a")
            (UVar "b"))))

----------------------------------------

-- localCompletenessOfSum aSumB
--   = case aSumB of
--       Left a -> Left a
--       Right b -> Right b
public export
ilocalCompletenessOfSum
   : {a, b : Ty}
  -> ICmd [Sum a b] [Sum a b]
ilocalCompletenessOfSum {a} {b}
  = iconsume
      [Sum a b] Here
      (IMatchSum
        a b
        (ICoMu a
          (iproduce
            [Sum a b] Here
            (ILeft
              a
              (IVar a))))
        (ICoMu b
          (iproduce
            [Sum a b] Here
            (IRight
              b
              (IVar b)))))

public export
ulocalCompletenessOfSum
   : UCmd
ulocalCompletenessOfSum
  = uconsume "in"
      (UMatchSum
        (UCoMu "a"
          (uproduce "out"
            (ULeft (UVar "a"))))
        (UCoMu "b"
          (uproduce "out"
            (URight (UVar "b")))))

----------------------------------------

-- fst (localCompletenessOfWith aWithB)
--   = fst aWithB
-- snd (localCompletenessOfWith aWithB)
--   = snd aWithB
public export
ilocalCompletenessOfWith
   : {a, b : Ty}
  -> ICmd [With a b] [With a b]
ilocalCompletenessOfWith {a} {b}
  = iproduce
      [With a b] Here
      (ICoMatchWith
        a b
        (IMu a
          (iconsume
            [With a b] Here
            (IFst
              a
              (ICoVar a))))
        (IMu b
          (iconsume
            [With a b] Here
            (ISnd
              b
              (ICoVar b)))))

public export
ulocalCompletenessOfWith
   : UCmd
ulocalCompletenessOfWith
  = uproduce "out"
      (UCoMatchWith
        (UMu "a"
          (uconsume "in"
            (UFst (UCoVar "a"))))
        (UMu "b"
          (uconsume "in"
            (USnd (UCoVar "b")))))

----------------------------------------

public export
ilocalCompletenessOfPar
   : {a, b : Ty}
  -> ICmd [Par a b] [Par a b]
ilocalCompletenessOfPar {a} {b}
  = iproduce
      [Par a b] Here
      (ICoMatchPar
        a b
        (iconsume
          [Par a b] Here
          (IHandlePar
            a b
            [] Nil
            [a, b] (PickLeft $ PickRight Nil)
            (ICoVar a)
            (ICoVar b))))

public export
ulocalCompletenessOfPar
   : UCmd
ulocalCompletenessOfPar
  = uproduce "out"
      (UCoMatchPar "a" "b"
        (uconsume "in"
          (UHandlePar
            (UCoVar "a")
            (UCoVar "b"))))