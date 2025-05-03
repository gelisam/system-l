-- This module implements an unusual version of the unification algorithm in
-- which unification variables can only stand for one possible value, namely
-- (). Nevertheless, as usual in a unification algorithm, we consider the
-- value of a unification variable to be unknown until it is unified with a
-- concrete type. The module "UnifyCtx.idr" uses this to track whether a given
-- 'PCtx' is extensible (unknown) or not (known to be ()).
module UTerm.UnifyExtensible

import Control.Monad.State

import Ty
import UTerm.UnionFind as UnionFind
import Util.ExceptT

----------------------------------------

fromExtensible : Bool -> Maybe ()
fromExtensible True
  = Nothing  -- unknown
fromExtensible False
  = Just ()  -- known to be ()

toExtensible : Maybe () -> Bool
toExtensible Nothing
  = True
toExtensible (Just ())
  = False

----------------------------------------

public export
UVarExtensible : Type
UVarExtensible = Node ()

public export
record UnifyExtensibleT (m : Type -> Type) (a : Type) where
  constructor MkUnifyExtensibleT
  unUnifyExtensibleT : UnionFindT () m a

public export
UnifyExtensible : Type -> Type
UnifyExtensible = UnifyExtensibleT Identity

-- Note that while it is common for a computation of type 'UnifyTy' to return a
-- 'PTy' and to generalize it to a 'PolyTy' at the same time, it is not common
-- for a 'UnifyExtensible' computation to return a 'UVarExtensible' and to
-- generalize it to ().  Therefore, we reserve the name 'runUnifyExtensible' for
-- the common function which does not generalize.
public export
runUnifyExtensibleT
   : Monad m
  => UnifyExtensibleT m a
  -> m a
runUnifyExtensibleT (MkUnifyExtensibleT body) = runUnionFindT $ do
  -- make sure node 0 ('nonExtensibleUVar') is not extensible
  _ <- newNode $ fromExtensible False

  body

public export
runUnifyExtensible
   : UnifyExtensible a
  -> a
runUnifyExtensible = runIdentity . runUnifyExtensibleT

-----------------------------------------

public export
implementation Monad m => Functor (UnifyExtensibleT m) where
  map f (MkUnifyExtensibleT m) = MkUnifyExtensibleT $ map f m

public export
implementation Monad m => Applicative (UnifyExtensibleT m) where
  pure x = MkUnifyExtensibleT $ pure x
  (MkUnifyExtensibleT f) <*> (MkUnifyExtensibleT x) = MkUnifyExtensibleT $ f <*> x

public export
implementation Monad m => Monad (UnifyExtensibleT m) where
  (MkUnifyExtensibleT ma) >>= f
    = MkUnifyExtensibleT (ma >>= \a => unUnifyExtensibleT (f a))

public export
implementation MonadTrans UnifyExtensibleT where
  lift = MkUnifyExtensibleT . lift

public export
implementation MonadUnionFind v m => MonadUnionFind v (UnifyExtensibleT m) where
  liftUnionFind = lift . liftUnionFind

-----------------------------------------

public export
nonExtensibleUVar : UVarExtensible
nonExtensibleUVar = MkNode 0

public export
newExtensibleUVar : Monad m => UnifyExtensibleT m UVarExtensible
newExtensibleUVar = MkUnifyExtensibleT $ do
  newNode $ fromExtensible True

public export
unifyUVarExtensibles
   : Monad m
  => UVarExtensible
  -> UVarExtensible
  -> UnifyExtensibleT m ()
unifyUVarExtensibles node1 node2 = MkUnifyExtensibleT $ do
  extensible1 <- toExtensible <$> getValue node1
  extensible2 <- toExtensible <$> getValue node2
  union node1 node2 $ fromExtensible (extensible1 && extensible2)

public export
getIsExtensible
   : Monad m
  => UVarExtensible
  -> UnifyExtensibleT m Bool
getIsExtensible node = MkUnifyExtensibleT $ do
  toExtensible <$> getValue node

----------------------------------------

example1 : UnifyExtensible (Bool, Bool, Bool, Bool)
example1 = do
  uvar1 <- newExtensibleUVar
  uvar2 <- newExtensibleUVar
  uvar3 <- newExtensibleUVar
  uvar4 <- newExtensibleUVar
  unifyUVarExtensibles uvar1 uvar2
  unifyUVarExtensibles uvar2 uvar3
  unifyUVarExtensibles uvar3 nonExtensibleUVar
  extensible1 <- getIsExtensible uvar1
  extensible2 <- getIsExtensible uvar2
  extensible3 <- getIsExtensible uvar3
  extensible4 <- getIsExtensible uvar4
  pure (extensible1, extensible2, extensible3, extensible4)

public export
test1 : IO ()
test1 = printLn ( runUnifyExtensible example1
               == ( False
                  , False
                  , False
                  , True
                  )
                )

----------------------------------------

public export
interface Monad m => MonadUnifyExtensible m where
  liftUnifyExtensible : UnifyExtensible a -> m a

public export
implementation Monad m => MonadUnifyExtensible (UnifyExtensibleT m) where
  liftUnifyExtensible body = MkUnifyExtensibleT $ go body
    where
      go : UnifyExtensible a -> UnionFindT () m a
      go body = do
        liftUnionFind $ unUnifyExtensibleT body

public export
implementation MonadUnifyExtensible m => MonadUnifyExtensible (StateT s m) where
  liftUnifyExtensible = lift . liftUnifyExtensible

public export
implementation MonadUnifyExtensible m => MonadUnifyExtensible (ExceptT e m) where
  liftUnifyExtensible = lift . liftUnifyExtensible
