-- "PolyTy" stands for "Polymorphic Type". System L itself does not have
-- polymorphic types, but it is very convenient to be able to write a definition
-- like
--
--   iapply : ICmd [Imp a b, a] [b]
--
-- once and to not have to write a different version for every types `a` and `b`
-- could stand for. Thus, while sub-terms cannot have a polymorphic type, we
-- allow the top-level definitions in "Example.idr" to have a polymorphic type.
-- This approach also makes it possible to accept UTerms whose type would
-- otherwise be ambiguous.
module UTerm.PolyTy

import Control.Monad.State
import Data.String as String

import Ty
import UTerm.UnionFind

----------------------------------------

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
PolyMinus : PolyTy -> PolyTy -> PolyTy
PolyMinus a b = Ctor (MinusF a b)

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

----------------------------------------

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
implementation Eq PolyTy where
  QVar i1 == QVar i2
    = i1 == i2
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
