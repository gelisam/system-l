import UnionFind

data Ty : Type where
  Imp : Ty -> Ty -> Ty
  Ten : Ty -> Ty -> Ty
  Sum : Ty -> Ty -> Ty
  With : Ty -> Ty -> Ty
  Par : Ty -> Ty -> Ty

data Elem : Ty -> List Ty -> Type where
  Here
     : {x : Ty}
    -> {xs : List Ty}
    -> Elem x (x :: xs)
  There
     : {x, y: Ty}
    -> {xs : List Ty}
    -> Elem x xs
    -> Elem x (y :: xs)

allButElem : Elem a g -> List Ty
allButElem (Here {x} {xs})
  = xs
allButElem (There {x} {y} {xs} xElemXs)
  = y :: allButElem xElemXs

data Cover : List Ty -> List Ty -> List Ty -> Type where
  Nil
     : Cover [] [] []
  PickLeft
     : Cover g d gd
    -> Cover (a::g) d (a::gd)
  PickRight
     : Cover g d gd
    -> Cover g (a::d) (a::gd)

allLeft
   : {g : List Ty}
  -> Cover g [] g
allLeft {g = []}
  = Nil
allLeft {g = a :: g}
  = PickLeft (allLeft {g})

allRight
   : {d : List Ty}
  -> Cover [] d d
allRight {d = []}
  = Nil
allRight {d = a :: d}
  = PickRight (allRight {d})

pickLeftFromElem
   : (xElemXs : Elem x xs)
  -> Cover [x] (allButElem xElemXs) xs
pickLeftFromElem Here
  = PickLeft allRight
pickLeftFromElem (There xElemXs)
  = PickRight (pickLeftFromElem xElemXs)

pickRightFromElem
   : (xElemXs : Elem x xs)
  -> Cover (allButElem xElemXs) [x] xs
pickRightFromElem Here
  = PickRight allLeft
pickRightFromElem (There xElemXs)
  = PickLeft (pickRightFromElem xElemXs)

-----------------
-- typed terms --
-----------------

mutual
  data Cmd : List Ty -> List Ty -> Type where
    Cut
       : (gg' : List Ty)
      -> Cover g g' gg'
      -> (dd' : List Ty)
      -> Cover d d' dd'
      -> Producer g a d
      -> Consumer g' a d'
      -> Cmd gg' dd'

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


----------------------------
-- example typed programs --
----------------------------

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

-- localCompletenessOfImp f
--   = \x -> f x
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


-------------------
-- untyped terms --
-------------------

mutual
  data UCmd : Type where
    UCut
       : UProducer
      -> UConsumer
      -> UCmd

  data UProducer : Type where
    UVar
       : String
      -> UProducer
    UMu
       : String
      -> UCmd
      -> UProducer
    ULam
       : String
      -> String
      -> UCmd
      -> UProducer
    UPair
       : UProducer
      -> UProducer
      -> UProducer
    ULeft
       : UProducer
      -> UProducer
    URight
       : UProducer
      -> UProducer
    UCoMatchWith
       : UProducer
      -> UProducer
      -> UProducer
    UCoMatchPar
       : String
      -> String
      -> UCmd
      -> UProducer

  data UConsumer : Type where
    UCoVar
       : String
      -> UConsumer
    UCoMu
       : String
      -> UCmd
      -> UConsumer
    UApp
       : UProducer
      -> UConsumer
      -> UConsumer
    UMatchPair
       : String
      -> String
      -> UCmd
      -> UConsumer
    UMatchSum
       : UConsumer
      -> UConsumer
      -> UConsumer
    UFst
       : UConsumer
      -> UConsumer
    USnd
       : UConsumer
      -> UConsumer
    UHandlePar
       : UConsumer
      -> UConsumer
      -> UConsumer


------------------------------
-- example untyped programs --
------------------------------

ucmdFromConsumer
   : String
  -> UConsumer
  -> UCmd
ucmdFromConsumer x consumer
  = UCut (UVar x) consumer

ucmdFromProducer
   : String
  -> UProducer
  -> UCmd
ucmdFromProducer x producer
  = UCut producer (UCoVar x)

ulocalCompletenessOfImp
   : UCmd
ulocalCompletenessOfImp
  = ucmdFromProducer "out"
      (ULam "a" "b"
        (ucmdFromConsumer "in"
          (UApp
            (UVar "a")
            (UCoVar "b"))))

ulocalCompletenessOfTen
   : UCmd
ulocalCompletenessOfTen
  = ucmdFromConsumer "in"
      (UMatchPair "a" "b"
        (ucmdFromProducer "out"
          (UPair
            (UVar "a")
            (UVar "b"))))

ulocalCompletenessOfSum
   : UCmd
ulocalCompletenessOfSum
  = ucmdFromConsumer "in"
      (UMatchSum
        (UCoMu "a"
          (ucmdFromProducer "out"
            (ULeft (UVar "a"))))
        (UCoMu "b"
          (ucmdFromProducer "out"
            (URight (UVar "b")))))

ulocalCompletenessOfWith
   : UCmd
ulocalCompletenessOfWith
  = ucmdFromProducer "out"
      (UCoMatchWith
        (UMu "a"
          (ucmdFromConsumer "in"
            (UFst (UCoVar "a"))))
        (UMu "b"
          (ucmdFromConsumer "in"
            (USnd (UCoVar "b")))))

ulocalCompletenessOfPar
   : UCmd
ulocalCompletenessOfPar
  = ucmdFromProducer "out"
      (UCoMatchPar "a" "b"
        (ucmdFromConsumer "in"
          (UHandlePar
            (UCoVar "a")
            (UCoVar "b"))))


main : IO ()
main = do
  putStrLn "typechecks."