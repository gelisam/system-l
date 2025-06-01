-- "UTerm" stands for "Untyped Term". I recommend comparing with "ITerm.idr",
-- which has the same structure but with more precise types, to clarify the
-- purpose of the sub-terms.
--
-- One important difference between ITerm and UTerm is that UTerm uses String
-- variable names to select {co,}variables, while with ITerm it is always the
-- {co,}variables at the front of the {co,}context which are used. As a result,
-- ITerm need to use ibring{,Co}VarToFront to reorder the variables in the
-- {,co}context, while UTerm does not.
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
    UGap
       : UProducer
      -> UConsumer
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
    UFillGap
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
    USplitPar
       : UConsumer
      -> UConsumer
      -> UConsumer

----------------------------------------

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
  showUProducer p (UGap producer consumer)
    = showParens (p /= Open)
    $ "UGap " ++ showUProducer App producer ++ " " ++ showUConsumer App consumer
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
  showUConsumer p (UFillGap x y cmd)
    = showParens (p /= Open)
    $ "UFillGap " ++ showPrec App x ++ " " ++ showPrec App y ++ " " ++ showUCmd App cmd
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
  showUConsumer p (USplitPar consumerA consumerB)
    = showParens (p /= Open)
    $ "USplitPar " ++ showUConsumer App consumerA ++ " " ++ showUConsumer App consumerB

public export
implementation Show UCmd where
  showPrec = showUCmd

public export
implementation Show UProducer where
  showPrec = showUProducer

public export
implementation Show UConsumer where
  showPrec = showUConsumer
