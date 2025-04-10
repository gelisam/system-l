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
    UConnect
       : UConsumer
      -> UProducer
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
    UMatchBridge
       : String
      -> String
      -> UCmd
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


mutual
  showUCmd : Prec -> UCmd -> String
  showUCmd p (UCut producer consumer)
    = showParens (p /= Open)
    $ "UCut " ++ showUProducer App producer ++ " " ++ showUConsumer App consumer

  showUProducer : Prec -> UProducer -> String
  showUProducer p (UVar x)
    = showParens (p /= Open)
    $ "UVar " ++ showPrec App x
  showUProducer p (UMu x cmd)
    = showParens (p /= Open)
    $ "UMu " ++ showPrec App x ++ " " ++ showUCmd App cmd
  showUProducer p (ULam x y cmd)
    = showParens (p /= Open)
    $ "ULam " ++ showPrec App x ++ " " ++ showPrec App y ++ " " ++ showUCmd App cmd
  showUProducer p (UConnect consumer producer)
    = showParens (p /= Open)
    $ "UConnect " ++ showUConsumer App consumer ++ " " ++ showUProducer App producer
  showUProducer p (UPair producer1 producer2)
    = showParens (p /= Open)
    $ "UPair " ++ showUProducer App producer1 ++ " " ++ showUProducer App producer2
  showUProducer p (ULeft producer)
    = showParens (p /= Open)
    $ "ULeft " ++ showUProducer App producer
  showUProducer p (URight producer)
    = showParens (p /= Open)
    $ "URight " ++ showUProducer App producer
  showUProducer p (UCoMatchWith producer1 producer2)
    = showParens (p /= Open)
    $ "UCoMatchWith " ++ showUProducer App producer1 ++ " " ++ showUProducer App producer2
  showUProducer p (UCoMatchPar x y cmd)
    = showParens (p /= Open)
    $ "UCoMatchPar " ++ showPrec App x ++ " " ++ showPrec App y ++ " " ++ showUCmd App cmd

  showUConsumer : Prec -> UConsumer -> String
  showUConsumer p (UCoVar x)
    = showParens (p /= Open)
    $ "UCoVar " ++ showPrec App x
  showUConsumer p (UCoMu x cmd)
    = showParens (p /= Open)
    $ "UCoMu " ++ showPrec App x ++ " " ++ showUCmd App cmd
  showUConsumer p (UApp producer consumer)
    = showParens (p /= Open)
    $ "UApp " ++ showUProducer App producer ++ " " ++ showUConsumer App consumer
  showUConsumer p (UMatchBridge x y cmd)
    = showParens (p /= Open)
    $ "UMatchBridge " ++ showPrec App x ++ " " ++ showPrec App y ++ " " ++ showUCmd App cmd
  showUConsumer p (UMatchPair x y cmd)
    = showParens (p /= Open)
    $ "UMatchPair " ++ showPrec App x ++ " " ++ showPrec App y ++ " " ++ showUCmd App cmd
  showUConsumer p (UMatchSum consumerA consumerB)
    = showParens (p /= Open)
    $ "UMatchSum " ++ showUConsumer App consumerA ++ " " ++ showUConsumer App consumerB
  showUConsumer p (UFst consumerA)
    = showParens (p /= Open)
    $ "UFst " ++ showUConsumer App consumerA
  showUConsumer p (USnd consumerB)
    = showParens (p /= Open)
    $ "USnd " ++ showUConsumer App consumerB
  showUConsumer p (UHandlePar consumerA consumerB)
    = showParens (p /= Open)
    $ "UHandlePar " ++ showUConsumer App consumerA ++ " " ++ showUConsumer App consumerB

public export
implementation Show UCmd where
  showPrec = showUCmd

public export
implementation Show UProducer where
  showPrec = showUProducer

public export
implementation Show UConsumer where
  showPrec = showUConsumer