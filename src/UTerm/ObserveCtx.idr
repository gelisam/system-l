-- A read-only API shared by UnifyCtx, UnifyCtxWithLog, UnifyCtxWithConstraints,
-- and UnifyCtxWithDisjointConstraints.
module UTerm.ObserveCtx

import Control.Monad.Identity
import Control.Monad.State

import Data.SortedMap as Map
import UTerm.PTy
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.ExceptT
import Util.Map as Map

public export
record PContext where
  constructor MkPContext
  varsSoFar
     : Map String PTy
  closed
     : Bool

public export
UVarCtx : Type
UVarCtx = Node PContext

Impl : Type -> Type
Impl = UnionFindT PContext UnifyTy

export
record ObserveCtx (a : Type) where
  constructor MkObserveCtx
  unObserveCtx : Impl a

-- @ObserveCtx -> Impl@ is allowed but @Impl -> ObserveCtx@ is not, since we
-- want to restrict the computation to read-only operations.
public export
runObserveCtx
  : ObserveCtx a
 -> UnionFindT PContext UnifyTy a
runObserveCtx (MkObserveCtx x) = x

getPContextImpl
   : UVarCtx
  -> Impl PContext
getPContextImpl node = do
  (liftUnionFind $ getValue node) >>= \case
    Nothing => do
      -- MonadUnifyCtx's API never stores Nothing, but to make the typechecker
      -- happy, we need to pick a dummy value for the unlikely case in which
      -- this function is called with a value which was not obtained via this
      -- API.
      pure $ MkPContext
        { varsSoFar
            = Map.empty
        , closed
            = True
        }
    Just pctx => do
      pure pctx

public export
zonkUVarCtx : UVarCtx -> ObserveCtx (Map String PTy)
zonkUVarCtx uvarCtx = MkObserveCtx $ do
  MkPContext varsSoFar_ _ <- getPContextImpl uvarCtx
  for varsSoFar_ $ \pty => do
    liftUnifyTy $ zonkPTy pty

public export
zonkDepthUVarCtx : Nat -> UVarCtx -> ObserveCtx (Map String PTy)
zonkDepthUVarCtx depth uvarCtx = MkObserveCtx $ do
  MkPContext varsSoFar_ _ <- getPContextImpl uvarCtx
  for varsSoFar_ $ \pty => do
    liftUnifyTy $ zonkDepthPTy depth pty

public export
getVarsSoFar : UVarCtx -> ObserveCtx (Map String PTy)
getVarsSoFar uvarCtx = MkObserveCtx $ do
  MkPContext varsSoFar_ _ <- getPContextImpl uvarCtx
  pure varsSoFar_

public export
isClosedUVarCtx : UVarCtx -> ObserveCtx Bool
isClosedUVarCtx uvarCtx = MkObserveCtx $ do
  MkPContext _ closed <- getPContextImpl uvarCtx
  pure closed

public export
isOpenUVarCtx : UVarCtx -> ObserveCtx Bool
isOpenUVarCtx uvarCtx = MkObserveCtx $ do
  MkPContext _ closed <- getPContextImpl uvarCtx
  pure (not closed)

----------------------------------------

public export
implementation Functor ObserveCtx where
  map f (MkObserveCtx x) = MkObserveCtx (map f x)

public export
implementation Applicative ObserveCtx where
  pure x = MkObserveCtx (pure x)
  MkObserveCtx f <*> MkObserveCtx x
    = MkObserveCtx (f <*> x)

public export
implementation Monad ObserveCtx where
  (MkObserveCtx ma) >>= f
    = MkObserveCtx (ma >>= \a => unObserveCtx (f a))

----------------------------------------

public export
interface Monad m => MonadObserveCtx m where
  liftObserveCtx : ObserveCtx a -> m a

public export
implementation MonadObserveCtx ObserveCtx where
  liftObserveCtx = id

public export
implementation MonadObserveCtx m => MonadObserveCtx (ExceptT e m) where
  liftObserveCtx body = do
    lift $ liftObserveCtx body

public export
implementation MonadObserveCtx m => MonadObserveCtx (StateT s m) where
  liftObserveCtx body = do
    lift $ liftObserveCtx body