module PTy

import Control.Monad.State

import Ty
import UnionFind


mutual
  -- Partial Type, meaning that part of the type can be a MetaVar
  public export
  data PTy : Type where
    MetaVar : Node -> PTy
    Ctor : CTy -> PTy

  -- Constructor-headed partial Type
  public export
  CTy : Type
  CTy = TyF PTy

public export
PImp : PTy -> PTy -> PTy
PImp a b = Ctor (ImpF a b)

public export
PBridge : PTy -> PTy -> PTy
PBridge a b = Ctor (BridgeF a b)

public export
PTen : PTy -> PTy -> PTy
PTen a b = Ctor (TenF a b)

public export
PSum : PTy -> PTy -> PTy
PSum a b = Ctor (SumF a b)

public export
PWith : PTy -> PTy -> PTy
PWith a b = Ctor (WithF a b)

public export
PPar : PTy -> PTy -> PTy
PPar a b = Ctor (ParF a b)

--         .--- Ty
--         |     | tyToCTy
--         |     v
-- tyToPTy |    CTy
--         |     | Ctor
--         |     v
--         '--> PTy

public export
tyToPTy : Ty -> PTy
tyToPTy (MkTy tyf)
  = Ctor (map tyToPTy tyf)

public export
tyToCTy : Ty -> CTy
tyToCTy (MkTy tyf)
  = map tyToPTy tyf

public export
implementation Show PTy where
  showPrec p (MetaVar node)
    = "?" ++ show node
  showPrec p (Ctor (ImpF a b))
    = showParens (p /= Open)
    $ "PImp " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (BridgeF a b))
    = showParens (p /= Open)
    $ "PBridge " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (TenF a b))
    = showParens (p /= Open)
    $ "PTen " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (SumF a b))
    = showParens (p /= Open)
    $ "PSum " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (WithF a b))
    = showParens (p /= Open)
    $ "PWith " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (ParF a b))
    = showParens (p /= Open)
    $ "PPar " ++ showPrec App a ++ " " ++ showPrec App b

public export
implementation Eq PTy where
  MetaVar node1 == MetaVar node2
    = node1 == node2
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