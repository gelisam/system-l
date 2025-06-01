-- Each program is repeated twice: once as an intrinsically-typed term, and once
-- as an untyped term. The goal is to show that the type-checker can reconstruct
-- a type which is equivalent to the intrinsic type, up to reordering.
module Examples

import Infer
import ITerm
import ITerm.Cover
import ITerm.Elem
import Ty
import UTerm
import UTerm.GeneralizeTy
import UTerm.PolyTy
import UTerm.PTy
import UTerm.UnifyTy

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

public export
test1 : IO ()
test1 = printLn ( (runInferCmd $ uanihilate "x" "anti-x")
               == Right ( [("x", QVar 0)]
                        , [("anti-x", QVar 0)]
                        )
                )

----------------------------------------

public export
ibringVarToFront
   : {a : Ty}
  -> (g : List Ty)
  -> (aElemG : Elem a g)
  -> {d : List Ty}
  -> ICmd (a :: allButElem aElemG) d
  -> ICmd g d
ibringVarToFront {a} g aElemG cmd
  = iconsume
      g aElemG
      (ICoMu a cmd)

-- no untyped equivalent since the order of variables is irrelevant

----------------------------------------

-- specialized version of 'ibringVarToFront' from the README
public export
iswap
   : {a, b : Ty}
  -> ICmd [Ten a b] [Ten b a]
iswap {a} {b}
  = iconsume
      [Ten a b] Here
      (IMatchPair
        a b
        (iproduce
          [Ten b a] Here
          (IPair
            b a
            [a, b] (PickRight $ PickLeft Nil)
            [] Nil
            (IVar b)
            (IVar a))))

public export
uswap
   : String
  -> String
  -> UCmd
uswap in_ out
  = uconsume in_
      (UMatchPair "x" "y"
        (uproduce out
          (UPair
            (UVar "y")
            (UVar "x"))))

public export
test2 : IO ()
test2 = printLn ( (runInferCmd $ uswap "in" "out")
               == Right ( [("in", PolyTen (QVar 0) (QVar 1))]
                        , [("out", PolyTen (QVar 1) (QVar 0))]
                        )
                )

----------------------------------------

public export
ibringCoVarToFront
   : {a : Ty}
  -> {g : List Ty}
  -> (d : List Ty)
  -> (aElemD : Elem a d)
  -> ICmd g (a :: allButElem aElemD)
  -> ICmd g d
ibringCoVarToFront {a} d aElemD cmd
  = iproduce
      d aElemD
      (IMu a cmd)

-- no untyped equivalent since the order of variables is irrelevant

----------------------------------------

public export
iequivalence
   : {a, b, c, d : Ty}
  -> ICmd [a, b] [c, d]
  -> ICmd [] [Imp (Ten a b) (Par c d)]
iequivalence {a} {b} {c} {d} cmd
  = iproduce
      [Imp (Ten a b) (Par c d)] Here
      (ILam
        (Ten a b) (Par c d)
        (iproduce
          [Par c d] Here
          (ICoMatchPar
            c d
            (iconsume
              [Ten a b] Here
              (IMatchPair
                a b
                cmd)))))

public export
uequivalence
   : UCmd
  -> UCmd
uequivalence cmd
  = uproduce "out"
      (ULam "ab" "cd"
        (uproduce "cd"
          (UCoMatchPar "c" "d"
            (uconsume "ab"
              (UMatchPair "a" "b"
                cmd)))))

----------------------------------------

public export
iapply
   : {a, b : Ty}
  -> ICmd [Imp a b, a] [b]
iapply {a} {b}
  = iconsume
      [Imp a b, a] Here
      (IApp
        a b
        [a] allLeft
        [b] allRight
        (IVar a)
        (ICoVar b))

public export
uapply
   : String
  -> String
  -> String
  -> UCmd
uapply f in_ out
  = uconsume f
      (UApp
        (UVar in_)
        (UCoVar out))

public export
test3 : IO ()
test3 = printLn ( (runInferCmd $ uapply "f" "a" "b")
               == Right ( [ ("a", QVar 0)
                          , ("f", PolyImp (QVar 0) (QVar 1))
                          ]
                        , [ ("b", QVar 1)
                          ]
                        )
                )

----------------------------------------

public export
icurry
   : {a, b, c : Ty}
  -> ICmd [a, b] [c]
  -> IProducer [] (Imp a (Imp b c)) []
icurry {a} {b} {c} cmd
  = ILam
      a (Imp b c)
      (iproduce
        [Imp b c] Here
        (ILam
          b c
          (the (ICmd [b, a] [c])
            (ibringVarToFront
              [b, a] (There Here)
              cmd))))

public export
ucurry
   : String
  -> String
  -> String
  -> UCmd
  -> UProducer
ucurry a b c cmd
  = ULam a "b2c"
      (uproduce "b2c"
        (ULam b c
          cmd))

----------------------------------------

public export
iuncurry
   : {a, b, c : Ty}
  -> IProducer [] (Imp a (Imp b c)) []
  -> ICmd [a, b] [c]
iuncurry {a} {b} {c} pa2b2c
  = ICut
      (Imp a (Imp b c))
      [a, b] allRight
      [c] allRight
      pa2b2c
      (IApp
        a (Imp b c)
        [a, b] (PickLeft $ PickRight Nil)
        [c] (PickRight Nil)
        (IVar a)
        (IApp
          b c
          [b] (PickLeft Nil)
          [c] (PickRight Nil)
          (IVar b)
          (ICoVar c)))

public export
uuncurry
   : String
  -> String
  -> String
  -> UProducer
  -> UCmd
uuncurry a b c pa2b2c
  = UCut
      pa2b2c
      (UApp
        (UVar a)
        (UApp
          (UVar b)
          (UCoVar c)))

----------------------------------------

public export
icurryMinus
   : {a, b, c : Ty}
  -> ICmd [a] [b, c]
  -> IConsumer [] (Minus (Minus a b) c) []
icurryMinus {a} {b} {c} cmd
  = IFillGap
      (Minus a b) c
      (iconsume
        [Minus a b] Here
        (IFillGap
          a b
          cmd))

public export
ucurryMinus
   : String
  -> String
  -> String
  -> UCmd
  -> UConsumer
ucurryMinus a b c cmd
  = UFillGap
      "aMinusB" c
      (uconsume
        "aMinusB"
        (UFillGap
          a b
          cmd))

----------------------------------------

public export
iuncurryMinus
   : {a, b, c : Ty}
  -> IConsumer [] (Minus (Minus a b) c) []
  -> ICmd [a] [b, c]
iuncurryMinus {a} {b} {c} cAMinusBMinusC
  = ICut
      (Minus (Minus a b) c)
      [a] allLeft
      [b, c] allLeft
      (IGap
        (Minus a b) c
        [a] allLeft
        [b, c] (PickLeft $ PickRight Nil)
        (IGap
          a b
          [a] allLeft
          [b] allRight
          (IVar a)
          (ICoVar b))
        (ICoVar c))
      cAMinusBMinusC

public export
uuncurryMinus
   : String
  -> String
  -> String
  -> UConsumer
  -> UCmd
uuncurryMinus a b c cAMinusBMinusC
  = UCut
      (UGap
        (UGap
          (UVar a)
          (UCoVar b))
        (UCoVar c))
      cAMinusBMinusC

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

public export
test4 : IO ()
test4 = printLn ( (runInferCmd $ ulocalCompletenessOfImp)
               == Right ( [("in", PolyImp (QVar 0) (QVar 1))]
                        , [("out", PolyImp (QVar 0) (QVar 1))]
                        )
                )

----------------------------------------

ilocalCompletenessOfMinus
   : {a, b : Ty}
  -> ICmd [Minus a b] [Minus a b]
ilocalCompletenessOfMinus {a} {b}
  = iconsume
      [Minus a b] Here
      (IFillGap
        a b
        (iproduce
          [b, Minus a b] (There Here)
          (IGap
            a b
            [a] allLeft
            [b] allRight
            (IVar a)
            (ICoVar b))))

ulocalCompletenessOfMinus
   : UCmd
ulocalCompletenessOfMinus
  = uconsume "in"
      (UFillGap
        "a" "b"
        (uproduce "out"
          (UGap
            (UVar "a")
            (UCoVar "b"))))

public export
test5 : IO ()
test5 = printLn ( (runInferCmd $ ulocalCompletenessOfMinus)
               == Right ( [("in", PolyMinus (QVar 0) (QVar 1))]
                        , [("out", PolyMinus (QVar 0) (QVar 1))]
                        )
                )

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

public export
test6 : IO ()
test6 = printLn ( (runInferCmd $ ulocalCompletenessOfTen)
               == Right ( [("in", PolyTen (QVar 0) (QVar 1))]
                        , [("out", PolyTen (QVar 0) (QVar 1))]
                        )
                )

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

public export
test7 : IO ()
test7 = printLn ( (runInferCmd $ ulocalCompletenessOfSum)
               == Right ( [("in", PolySum (QVar 0) (QVar 1))]
                        , [("out", PolySum (QVar 0) (QVar 1))]
                        )
                )

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

public export
test8 : IO ()
test8 = printLn ( (runInferCmd $ ulocalCompletenessOfWith)
               == Right ( [("in", PolyWith (QVar 0) (QVar 1))]
                        , [("out", PolyWith (QVar 0) (QVar 1))]
                        )
                )

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
          (ISplitPar
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
          (USplitPar
            (UCoVar "a")
            (UCoVar "b"))))

public export
test9 : IO ()
test9 = printLn ( (runInferCmd $ ulocalCompletenessOfPar)
               == Right ( [("in", PolyPar (QVar 0) (QVar 1))]
                        , [("out", PolyPar (QVar 0) (QVar 1))]
                        )
                )
