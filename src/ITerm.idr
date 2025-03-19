-- intrinsically-typed terms
module ITerm

import Cover
import Elem
import Ty


mutual
  public export
  data ICmd : List Ty -> List Ty -> Type where
    ICut
       : (gg' : List Ty)
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
       : ICmd (a::g) (b::d)
      -> IProducer g (Imp a b) d
    IPair
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IProducer g a d
      -> IProducer g' b d'
      -> IProducer gg' (Ten a b) dd'
    ILeft
       : IProducer g a d
      -> IProducer g (Sum a b) d
    IRight
       : IProducer g b d
      -> IProducer g (Sum a b) d
    ICoMatchWith
       : IProducer g a d
      -> IProducer g b d
      -> IProducer g (With a b) d
    ICoMatchPar
       : ICmd g (a::b::d)
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
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> IProducer g a d
      -> IConsumer g' b d'
      -> IConsumer gg' (Imp a b) dd'
    IMatchPair
       : ICmd (a::b::g) d
      -> IConsumer g (Ten a b) d
    IMatchSum
       : IConsumer g a d
      -> IConsumer g b d
      -> IConsumer g (Sum a b) d
    IFst
       : IConsumer g a d
      -> IConsumer g (With a b) d
    ISnd
       : IConsumer g b d
      -> IConsumer g (With a b) d
    IHandlePar
       : (gg' : List Ty)
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
icmdFromConsumer
   : (g : List Ty)
  -> {a : Ty}
  -> {d : List Ty}
  -> (xElemXs : Elem a g)
  -> IConsumer (allButElem xElemXs) a d
  -> ICmd g d
icmdFromConsumer g {a} {d} xElemXs consumer
  = ICut
      g (pickLeftFromElem xElemXs)
      d allRight
      (IVar a)
      consumer

public export
icmdFromProducer
   : {g : List Ty}
  -> {a : Ty}
  -> (d : List Ty)
  -> (xElemXs : Elem a d)
  -> IProducer g a (allButElem xElemXs)
  -> ICmd g d
icmdFromProducer {g} {a} d xElemXs producer
  = ICut
      g allLeft
      d (pickRightFromElem xElemXs)
      producer
      (ICoVar a)

public export
ianihilateSingleton
   : {a : Ty}
  -> ICmd [a] [a]
ianihilateSingleton {a}
  = ICut
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
  = icmdFromConsumer (b :: a :: g) (There Here)
      (ICoMu a cmd)

public export
iswapCoVars
   : {a, b : Ty}
  -> {g, d : List Ty}
  -> ICmd g (a :: b :: d)
  -> ICmd g (b :: a :: d)
iswapCoVars {a} {b} {g} {d} cmd
  = icmdFromProducer (b :: a :: d) (There Here)
      (IMu a cmd)

-- localCompletenessOfImp f
--   = \x -> f x
public export
ilocalCompletenessOfImp
   : {a, b : Ty}
  -> ICmd [Imp a b] [Imp a b]
ilocalCompletenessOfImp {a} {b}
  = icmdFromProducer [Imp a b] Here
      (ILam
        (icmdFromConsumer [a, Imp a b] (There Here)
          (IApp
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
  = icmdFromConsumer [Ten a b] Here
      (IMatchPair
        (icmdFromProducer [Ten a b] Here
          (IPair
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
  = icmdFromConsumer [Sum a b] Here
      (IMatchSum
        (ICoMu a
          (icmdFromProducer [Sum a b] Here
            (ILeft (IVar a))))
        (ICoMu b
          (icmdFromProducer [Sum a b] Here
            (IRight (IVar b)))))

-- fst (localCompletenessOfWith aWithB)
--   = fst aWithB
-- snd (localCompletenessOfWith aWithB)
--   = snd aWithB
public export
ilocalCompletenessOfWith
   : {a, b : Ty}
  -> ICmd [With a b] [With a b]
ilocalCompletenessOfWith {a} {b}
  = icmdFromProducer [With a b] Here
      (ICoMatchWith
        (IMu a
          (icmdFromConsumer [With a b] Here
            (IFst (ICoVar a))))
        (IMu b
          (icmdFromConsumer [With a b] Here
            (ISnd (ICoVar b)))))

public export
ilocalCompletenessOfPar
   : {a, b : Ty}
  -> ICmd [Par a b] [Par a b]
ilocalCompletenessOfPar {a} {b}
  = icmdFromProducer [Par a b] Here
      (ICoMatchPar
        (icmdFromConsumer [Par a b] Here
          (IHandlePar
            [] Nil
            [a, b] (PickLeft $ PickRight Nil)
            (ICoVar a)
            (ICoVar b))))
