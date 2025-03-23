-- intrinsically-typed terms
module ITerm

import Cover
import Elem
import Ty


mutual
  -- `ICmd [a, b] [c, d]` is equivalent to `ICmd [] [Imp (Ten a b) (Par c d)]`.
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

  -- `IProducer g a d` is equivalent to `ICmd g (a :: d)`.
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

  -- `IConsumer g a d` is equivalent to `Cmd (a :: g) d`.
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