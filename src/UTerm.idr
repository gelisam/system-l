-- untyped terms
module UTerm


mutual
  public export
  data UCmd : Type where
    UCut
       : UProducer
      -> UConsumer
      -> UCmd

  public export
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

  public export
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

public export
uconsume
   : String
  -> UConsumer
  -> UCmd
uconsume x consumer
  = UCut (UVar x) consumer

public export
uproduce
   : String
  -> UProducer
  -> UCmd
uproduce x producer
  = UCut producer (UCoVar x)

public export
uanihilate
   : String
  -> String
  -> UCmd
uanihilate x cox
  = UCut (UVar x) (UCoVar cox)

public export
uswapVars
   : String
  -> String
  -> UCmd
  -> UCmd
uswapVars a b cmd
  = uconsume a
      (UCoMu a cmd)


public export
uswapCoVars
   : String
  -> String
  -> UCmd
  -> UCmd
uswapCoVars a b cmd
  = uproduce a
      (UMu a cmd)

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
ulocalCompletenessOfPar
   : UCmd
ulocalCompletenessOfPar
  = uproduce "out"
      (UCoMatchPar "a" "b"
        (uconsume "in"
          (UHandlePar
            (UCoVar "a")
            (UCoVar "b"))))
