-- intrinsically-typed terms
module Term

import Cover
import Elem
import Ty


mutual
  public export
  data Cmd : List Ty -> List Ty -> Type where
    Cut
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> Producer g a d
      -> Consumer g' a d'
      -> Cmd gg' dd'

  public export
  data Producer : List Ty -> Ty -> List Ty -> Type where
    Var
       : (a : Ty)
      -> Producer [a] a []
    Mu
       : (a : Ty)
      -> Cmd g (a::d)
      -> Producer g a d
    Lam
       : Cmd (a::g) (b::d)
      -> Producer g (Imp a b) d
    Pair
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> Producer g a d
      -> Producer g' b d'
      -> Producer gg' (Ten a b) dd'
    Left
       : Producer g a d
      -> Producer g (Sum a b) d
    Right
       : Producer g b d
      -> Producer g (Sum a b) d
    CoMatchWith
       : Producer g a d
      -> Producer g b d
      -> Producer g (With a b) d
    CoMatchPar
       : Cmd g (a::b::d)
      -> Producer g (Par a b) d

  public export
  data Consumer : List Ty -> Ty -> List Ty -> Type where
    CoVar
       : (a : Ty)
      -> Consumer [] a [a]
    CoMu
       : (a : Ty)
      -> Cmd (a::g) d
      -> Consumer g a d
    App
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> Producer g a d
      -> Consumer g' b d'
      -> Consumer gg' (Imp a b) dd'
    MatchPair
       : Cmd (a::b::g) d
      -> Consumer g (Ten a b) d
    MatchSum
       : Consumer g a d
      -> Consumer g b d
      -> Consumer g (Sum a b) d
    Fst
       : Consumer g a d
      -> Consumer g (With a b) d
    Snd
       : Consumer g b d
      -> Consumer g (With a b) d
    HandlePar
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> Consumer g a d
      -> Consumer g' b d'
      -> Consumer gg' (Par a b) dd'


----------------------
-- example programs --
----------------------

public export
cmdFromConsumer
   : (g : List Ty)
  -> {a : Ty}
  -> {d : List Ty}
  -> (xElemXs : Elem a g)
  -> Consumer (allButElem xElemXs) a d
  -> Cmd g d
cmdFromConsumer g {a} {d} xElemXs consumer
  = Cut
      g (pickLeftFromElem xElemXs)
      d allRight
      (Var a)
      consumer

public export
cmdFromProducer
   : {g : List Ty}
  -> {a : Ty}
  -> (d : List Ty)
  -> (xElemXs : Elem a d)
  -> Producer g a (allButElem xElemXs)
  -> Cmd g d
cmdFromProducer {g} {a} d xElemXs producer
  = Cut
      g allLeft
      d (pickRightFromElem xElemXs)
      producer
      (CoVar a)

public export
anihilateSingleton
   : {a : Ty}
  -> Cmd [a] [a]
anihilateSingleton {a}
  = Cut
      [a] allLeft
      [a] allRight
      (Var a)
      (CoVar a)

public export
swapVars
   : {a, b : Ty}
  -> {g, d : List Ty}
  -> Cmd (a :: b :: g) d
  -> Cmd (b :: a :: g) d
swapVars {a} {b} {g} {d} cmd
  = cmdFromConsumer (b :: a :: g) (There Here)
      (CoMu a cmd)

public export
swapCoVars
   : {a, b : Ty}
  -> {g, d : List Ty}
  -> Cmd g (a :: b :: d)
  -> Cmd g (b :: a :: d)
swapCoVars {a} {b} {g} {d} cmd
  = cmdFromProducer (b :: a :: d) (There Here)
      (Mu a cmd)

-- localCompletenessOfImp f
--   = \x -> f x
public export
localCompletenessOfImp
   : {a, b : Ty}
  -> Cmd [Imp a b] [Imp a b]
localCompletenessOfImp {a} {b}
  = cmdFromProducer [Imp a b] Here
      (Lam
        (cmdFromConsumer [a, Imp a b] (There Here)
          (App
            [a] (PickLeft Nil)
            [b] (PickRight Nil)
            (Var a)
            (CoVar b))))

-- localCompletenessOfTen aTenB
--   = case aTenB of
--       (a, b) -> Pair a b
public export
localCompletenessOfTen
   : {a, b : Ty}
  -> Cmd [Ten a b] [Ten a b]
localCompletenessOfTen {a} {b}
  = cmdFromConsumer [Ten a b] Here
      (MatchPair
        (cmdFromProducer [Ten a b] Here
          (Pair
            [a, b] (PickLeft $ PickRight Nil)
            [] Nil
            (Var a)
            (Var b))))

-- localCompletenessOfSum aSumB
--   = case aSumB of
--       Left a -> Left a
--       Right b -> Right b
public export
localCompletenessOfSum
   : {a, b : Ty}
  -> Cmd [Sum a b] [Sum a b]
localCompletenessOfSum {a} {b}
  = cmdFromConsumer [Sum a b] Here
      (MatchSum
        (CoMu a
          (cmdFromProducer [Sum a b] Here
            (Left (Var a))))
        (CoMu b
          (cmdFromProducer [Sum a b] Here
            (Right (Var b)))))

-- fst (localCompletenessOfWith aWithB)
--   = fst aWithB
-- snd (localCompletenessOfWith aWithB)
--   = snd aWithB
public export
localCompletenessOfWith
   : {a, b : Ty}
  -> Cmd [With a b] [With a b]
localCompletenessOfWith {a} {b}
  = cmdFromProducer [With a b] Here
      (CoMatchWith
        (Mu a
          (cmdFromConsumer [With a b] Here
            (Fst (CoVar a))))
        (Mu b
          (cmdFromConsumer [With a b] Here
            (Snd (CoVar b)))))

public export
localCompletenessOfPar
   : {a, b : Ty}
  -> Cmd [Par a b] [Par a b]
localCompletenessOfPar {a} {b}
  = cmdFromProducer [Par a b] Here
      (CoMatchPar
        (cmdFromConsumer [Par a b] Here
          (HandlePar
            [] Nil
            [a, b] (PickLeft $ PickRight Nil)
            (CoVar a)
            (CoVar b))))
