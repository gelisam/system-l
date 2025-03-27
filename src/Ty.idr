-- types (connectives)
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
