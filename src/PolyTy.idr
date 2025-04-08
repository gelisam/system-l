module PolyTy

import Control.Monad.State
import Data.String as String

import Ty
import UnionFind


mutual
  -- Polymorphic Type, with quantified type variables
  public export
  data PolyTy : Type where
    QVar : Nat -> PolyTy
    Ctor : TyF PolyTy -> PolyTy

public export
PolyImp : PolyTy -> PolyTy -> PolyTy
PolyImp a b = Ctor (ImpF a b)

public export
PolyBridge : PolyTy -> PolyTy -> PolyTy
PolyBridge a b = Ctor (BridgeF a b)

public export
PolyTen : PolyTy -> PolyTy -> PolyTy
PolyTen a b = Ctor (TenF a b)

public export
PolySum : PolyTy -> PolyTy -> PolyTy
PolySum a b = Ctor (SumF a b)

public export
PolyWith : PolyTy -> PolyTy -> PolyTy
PolyWith a b = Ctor (WithF a b)

public export
PolyPar : PolyTy -> PolyTy -> PolyTy
PolyPar a b = Ctor (ParF a b)

public export
tyToPolyTy : Ty -> PolyTy
tyToPolyTy (MkTy tyf)
  = Ctor (map tyToPolyTy tyf)

public export
implementation Show PolyTy where
  showPrec p (QVar i)
    = if i < 26
      then String.singleton (chr (cast i + ord 'a'))
      else String.singleton (chr ((cast i `mod` 26) + ord 'a'))
        ++ show (cast i `div` 26)
  showPrec p (Ctor (ImpF a b))
    = showParens (p /= Open)
    $ "Imp " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (BridgeF a b))
    = showParens (p /= Open)
    $ "Bridge " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (TenF a b))
    = showParens (p /= Open)
    $ "Ten " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (SumF a b))
    = showParens (p /= Open)
    $ "Sum " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (WithF a b))
    = showParens (p /= Open)
    $ "With " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (ParF a b))
    = showParens (p /= Open)
    $ "Par " ++ showPrec App a ++ " " ++ showPrec App b

public export
implementation Eq PolyTy where
  QVar i1 == QVar i2
    = i1 == i2
  Ctor (ImpF a1 b1) == Ctor (ImpF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (BridgeF a1 b1) == Ctor (BridgeF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (TenF a1 b1) == Ctor (TenF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (SumF a1 b1) == Ctor (SumF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (WithF a1 b1) == Ctor (WithF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (ParF a1 b1) == Ctor (ParF a2 b2)
    = a1 == a2
   && b1 == b2
  _ == _
    = False
