-- intrinsically-typed terms
module ITerm

import Cover
import Elem
import Ty


mutual
  public export
  data ICmd : List Ty -> List Ty -> Type where
    ICut
       : (a : Ty)
      -> (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IProducer g a d
      -> IConsumer g' a d'
      -> ICmd gg' dd'

  public export
  data IProducer : List Ty -> Ty -> List Ty -> Type where
    IVar
       : (a : Ty)
      -> IProducer [a] a []
    IMu
       : (a : Ty)
      -> ICmd g (a::d)
      -> IProducer g a d
    ILam
       : (a, b : Ty)
      -> ICmd (a::g) (b::d)
      -> IProducer g (Imp a b) d
    IPair
       : (a, b : Ty)
      -> (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IProducer g a d
      -> IProducer g' b d'
      -> IProducer gg' (Ten a b) dd'
    ILeft
       : (a : Ty)
      -> IProducer g a d
      -> IProducer g (Sum a b) d
    IRight
       : (b : Ty)
      -> IProducer g b d
      -> IProducer g (Sum a b) d
    ICoMatchWith
       : (a, b : Ty)
      -> IProducer g a d
      -> IProducer g b d
      -> IProducer g (With a b) d
    ICoMatchPar
       : (a, b : Ty)
      -> ICmd g (a::b::d)
      -> IProducer g (Par a b) d

  public export
  data IConsumer : List Ty -> Ty -> List Ty -> Type where
    ICoVar
       : (a : Ty)
      -> IConsumer [] a [a]
    ICoMu
       : (a : Ty)
      -> ICmd (a::g) d
      -> IConsumer g a d
    IApp
       : (a, b : Ty)
      -> (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IProducer g a d
      -> IConsumer g' b d'
      -> IConsumer gg' (Imp a b) dd'
    IMatchPair
       : (a, b : Ty)
      -> ICmd (a::b::g) d
      -> IConsumer g (Ten a b) d
    IMatchSum
       : (a, b : Ty)
      -> IConsumer g a d
      -> IConsumer g b d
      -> IConsumer g (Sum a b) d
    IFst
       : (a : Ty)
      -> IConsumer g a d
      -> IConsumer g (With a b) d
    ISnd
       : (b : Ty)
      -> IConsumer g b d
      -> IConsumer g (With a b) d
    IHandlePar
       : (a, b : Ty)
      -> (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IConsumer g a d
      -> IConsumer g' b d'
      -> IConsumer gg' (Par a b) dd'


----------------------
-- example programs --
----------------------

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
iswapVars
   : {a, b : Ty}
  -> {g, d : List Ty}
  -> ICmd (a :: b :: g) d
  -> ICmd (b :: a :: g) d
iswapVars {a} {b} {g} {d} cmd
  = iconsume
      (b :: a :: g) (There Here)
      (ICoMu a cmd)

public export
iswapCoVars
   : {a, b : Ty}
  -> {g, d : List Ty}
  -> ICmd g (a :: b :: d)
  -> ICmd g (b :: a :: d)
iswapCoVars {a} {b} {g} {d} cmd
  = iproduce
      (b :: a :: d) (There Here)
      (IMu a cmd)

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
