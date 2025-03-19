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
ucmdFromConsumer
   : String
  -> UConsumer
  -> UCmd
ucmdFromConsumer x consumer
  = UCut (UVar x) consumer

public export
ucmdFromProducer
   : String
  -> UProducer
  -> UCmd
ucmdFromProducer x producer
  = UCut producer (UCoVar x)

public export
uanihilateSingleton
   : String
  -> String
  -> UCmd
uanihilateSingleton x cox
  = UCut (UVar x) (UCoVar cox)

public export
uswapVars
   : String
  -> String
  -> UCmd
  -> UCmd
uswapVars a b cmd
  = ucmdFromConsumer a
      (UCoMu a cmd)


public export
uswapCoVars
   : String
  -> String
  -> UCmd
  -> UCmd
uswapCoVars a b cmd
  = ucmdFromProducer a
      (UMu a cmd)

public export
ulocalCompletenessOfImp
   : UCmd
ulocalCompletenessOfImp
  = ucmdFromProducer "out"
      (ULam "a" "b"
        (ucmdFromConsumer "in"
          (UApp
            (UVar "a")
            (UCoVar "b"))))

public export
ulocalCompletenessOfTen
   : UCmd
ulocalCompletenessOfTen
  = ucmdFromConsumer "in"
      (UMatchPair "a" "b"
        (ucmdFromProducer "out"
          (UPair
            (UVar "a")
            (UVar "b"))))

public export
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

public export
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

public export
ulocalCompletenessOfPar
   : UCmd
ulocalCompletenessOfPar
  = ucmdFromProducer "out"
      (UCoMatchPar "a" "b"
        (ucmdFromConsumer "in"
          (UHandlePar
            (UCoVar "a")
            (UCoVar "b"))))
