-- "Ty" stands for "Type". See also "PTy" and "PolyTy", which are variants of
-- "Ty" implemented with the same underlying "TyF" base functor.
module Ty

public export
data TyF : Type -> Type where
  ImpF : r -> r -> TyF r
  BridgeF : r -> r -> TyF r
  TenF : r -> r -> TyF r
  SumF : r -> r -> TyF r
  WithF : r -> r -> TyF r
  ParF : r -> r -> TyF r

public export
data Ty : Type where
  MkTy : TyF Ty -> Ty

public export
Imp : Ty -> Ty -> Ty
Imp a b = MkTy (ImpF a b)

public export
Bridge : Ty -> Ty -> Ty
Bridge a b = MkTy (BridgeF a b)

public export
Ten : Ty -> Ty -> Ty
Ten a b = MkTy (TenF a b)

public export
Sum : Ty -> Ty -> Ty
Sum a b = MkTy (SumF a b)

public export
With : Ty -> Ty -> Ty
With a b = MkTy (WithF a b)

public export
Par : Ty -> Ty -> Ty
Par a b = MkTy (ParF a b)

----------------------------------------

public export
implementation Show r => Show (TyF r) where
  showPrec p (ImpF a b)
    = showParens (p /= Open)
    $ "ImpF " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (BridgeF a b)
    = showParens (p /= Open)
    $ "BridgeF " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (TenF a b)
    = showParens (p /= Open)
    $ "TenF " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (SumF a b)
    = showParens (p /= Open)
    $ "SumF " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (WithF a b)
    = showParens (p /= Open)
    $ "WithF " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (ParF a b)
    = showParens (p /= Open)
    $ "ParF " ++ showPrec App a ++ " " ++ showPrec App b

public export
implementation Eq r => Eq (TyF r) where
  ImpF a1 b1 == ImpF a2 b2
    = a1 == a2
   && b1 == b2
  BridgeF a1 b1 == BridgeF a2 b2
    = a1 == a2
   && b1 == b2
  TenF a1 b1 == TenF a2 b2
    = a1 == a2
   && b1 == b2
  SumF a1 b1 == SumF a2 b2
    = a1 == a2
   && b1 == b2
  WithF a1 b1 == WithF a2 b2
    = a1 == a2
   && b1 == b2
  ParF a1 b1 == ParF a2 b2
    = a1 == a2
   && b1 == b2
  _ == _
    = False

public export
implementation Functor TyF where
  map f (ImpF a b)
    = ImpF (f a) (f b)
  map f (BridgeF a b)
    = BridgeF (f a) (f b)
  map f (TenF a b)
    = TenF (f a) (f b)
  map f (SumF a b)
    = SumF (f a) (f b)
  map f (WithF a b)
    = WithF (f a) (f b)
  map f (ParF a b)
    = ParF (f a) (f b)

public export
implementation Foldable TyF where
  foldr f z (ImpF a b)
    = f a (f b z)
  foldr f z (BridgeF a b)
    = f a (f b z)
  foldr f z (TenF a b)
    = f a (f b z)
  foldr f z (SumF a b)
    = f a (f b z)
  foldr f z (WithF a b)
    = f a (f b z)
  foldr f z (ParF a b)
    = f a (f b z)

public export
implementation Traversable TyF where
  traverse f (ImpF a b)
    = ImpF <$> f a <*> f b
  traverse f (BridgeF a b)
    = BridgeF <$> f a <*> f b
  traverse f (TenF a b)
    = TenF <$> f a <*> f b
  traverse f (SumF a b)
    = SumF <$> f a <*> f b
  traverse f (WithF a b)
    = WithF <$> f a <*> f b
  traverse f (ParF a b)
    = ParF <$> f a <*> f b

public export
implementation Show Ty where
  showPrec p (MkTy (ImpF a b))
    = showParens (p /= Open)
    $ "Imp " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (MkTy (BridgeF a b))
    = showParens (p /= Open)
    $ "Bridge " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (MkTy (TenF a b))
    = showParens (p /= Open)
    $ "Ten " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (MkTy (SumF a b))
    = showParens (p /= Open)
    $ "Sum " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (MkTy (WithF a b))
    = showParens (p /= Open)
    $ "With " ++ showPrec App a ++ " " ++ showPrec App b
  showPrec p (MkTy (ParF a b))
    = showParens (p /= Open)
    $ "Par " ++ showPrec App a ++ " " ++ showPrec App b

public export
implementation Eq Ty where
  MkTy (ImpF a1 b1) == MkTy (ImpF a2 b2)
    = a1 == a2
   && b1 == b2
  MkTy (BridgeF a1 b1) == MkTy (BridgeF a2 b2)
    = a1 == a2
   && b1 == b2
  MkTy (TenF a1 b1) == MkTy (TenF a2 b2)
    = a1 == a2
   && b1 == b2
  MkTy (SumF a1 b1) == MkTy (SumF a2 b2)
    = a1 == a2
   && b1 == b2
  MkTy (WithF a1 b1) == MkTy (WithF a2 b2)
    = a1 == a2
   && b1 == b2
  MkTy (ParF a1 b1) == MkTy (ParF a2 b2)
    = a1 == a2
   && b1 == b2
  _ == _
    = False