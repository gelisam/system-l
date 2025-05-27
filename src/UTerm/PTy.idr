-- "PTy" stands for "Partial Type". The unification algorithm in "UnifyTy.idr"
-- works by keeping track of what is known so far about a type, that is, it
-- tracks partial information using a partial type. The unknown parts of the
-- type are represented by unification variables, so that when unifying two
-- partial types, the algorithm can track that two unknown parts in
-- corresponding positions are known to be the same type. For example, if we
-- learn that
--
--   PImp ?0 Nat == PImp ?1 Nat
--
-- then
--
--   PImp String Nat == PImp String Nat
--
-- would be a valid solution to this equation but
--
--   PImp String Nat == PImp Char Nat
--
-- would be an invalid solution.
module UTerm.PTy

import Control.Monad.State

import Ty
import UTerm.UnionFind

----------------------------------------

mutual
  -- Partial Type, meaning that part of the type can be a UVarTy
  public export
  data PTy : Type where
    UVarTy : Node CTy -> PTy
    Ctor : CTy -> PTy

  -- Constructor-headed partial Type
  public export
  CTy : Type
  CTy = TyF PTy

public export
PImp : PTy -> PTy -> PTy
PImp a b = Ctor (ImpF a b)

public export
PMinus : PTy -> PTy -> PTy
PMinus a b = Ctor (MinusF a b)

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

----------------------------------------

public export
implementation Show PTy where
  showPrec p (UVarTy (MkNode i))
    = "?" ++ show i
  showPrec p (Ctor (ImpF a b))
    = showParens (p /= Open)
    $ "Imp " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (Ctor (MinusF a b))
    = showParens (p /= Open)
    $ "Minus " ++ showPrec App a ++ " " ++ showPrec App b
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
implementation Eq PTy where
  UVarTy node1 == UVarTy node2
    = node1 == node2
  Ctor (ImpF a1 b1) == Ctor (ImpF a2 b2)
    = a1 == a2
   && b1 == b2
  Ctor (MinusF a1 b1) == Ctor (MinusF a2 b2)
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
