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