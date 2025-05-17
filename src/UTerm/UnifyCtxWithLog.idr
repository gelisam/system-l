-- UnifyCtxWithLog is a helper for UnifyCtxWithConstraints. In that module,
-- event handlers are allowed to react to an event by inserting new variables
-- and closing contexts, but not by creating new unification variables. The
-- UnifyCtxWithLog monad only provides those two operations, and is thus how
-- handlers are implemented.
--
-- The WithLog part is that each operation is added to a list of events, so that
-- the handlers can react to the operations performed by other handlers.
module UTerm.UnifyCtxWithLog

import Control.Monad.State
import Data.SortedMap as Map

import UTerm.PTy
import UTerm.UnifyCtx as UnifyCtx
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.Map as Map

----------------------------------------

public export
data UnifyCtxEvent
  = Added UVarCtx String
  | Closed UVarCtx

export
record UnifyCtxWithLogT (m : Type -> Type) (a : Type) where
  constructor MkUnifyCtxWithLogT
  unUnifyCtxWithLogT : StateT (List UnifyCtxEvent) (UnifyCtxT m) a

public export
UnifyCtxWithLog : Type -> Type
UnifyCtxWithLog = UnifyCtxWithLogT Identity

public export
runUnifyCtxWithLogT
   : Monad m
  => UnifyCtxWithLogT m a
  -> StateT (List UnifyCtxEvent) (UnifyCtxT m) a
runUnifyCtxWithLogT = unUnifyCtxWithLogT

public export
runUnifyCtxWithLog
   : UnifyCtxWithLog a
  -> StateT (List UnifyCtxEvent) UnifyCtx a
runUnifyCtxWithLog = runUnifyCtxWithLogT

----------------------------------------

public export
implementation Monad m => Functor (UnifyCtxWithLogT m) where
  map f (MkUnifyCtxWithLogT m) = MkUnifyCtxWithLogT $ map f m

public export
implementation Monad m => Applicative (UnifyCtxWithLogT m) where
  pure x = MkUnifyCtxWithLogT $ pure x
  MkUnifyCtxWithLogT f <*> MkUnifyCtxWithLogT x
    = MkUnifyCtxWithLogT (f <*> x)

public export
implementation Monad m => Monad (UnifyCtxWithLogT m) where
  (MkUnifyCtxWithLogT ma) >>= f
    = MkUnifyCtxWithLogT (ma >>= \a => unUnifyCtxWithLogT (f a))

-- 'm' operations are allowed as well, but they are not logged.
public export
implementation MonadTrans UnifyCtxWithLogT where
  lift = MkUnifyCtxWithLogT . lift . lift

----------------------------------------

-- Note that newUVarCtx is not provided: it is only possible to provide more
-- information about the existing UVarCtx, not to deepen the mystery.

public export
getVarsSoFar
   : Monad m
  => UVarCtx
  -> UnifyCtxWithLogT m (Map String PTy)
getVarsSoFar uvarCtx = MkUnifyCtxWithLogT $ do
  lift $ UnifyCtx.getVarsSoFar uvarCtx

public export
isClosedUVarCtx
   : Monad m
  => UVarCtx
  -> UnifyCtxWithLogT m Bool
isClosedUVarCtx uvarCtx = MkUnifyCtxWithLogT $ do
  lift $ UnifyCtx.isClosedUVarCtx uvarCtx

public export
isOpenUVarCtx
   : Monad m
  => UVarCtx
  -> UnifyCtxWithLogT m Bool
isOpenUVarCtx uvarCtx = MkUnifyCtxWithLogT $ do
  lift $ UnifyCtx.isOpenUVarCtx uvarCtx

-- Logs an 'Added' event if the variable was not previously in the context.
public export
insert
   : Monad m
  => UVarCtx
  -> String
  -> PTy
  -> UnifyCtxWithLogT m ()
insert uvarCtx x pty = MkUnifyCtxWithLogT $ do
  -- Get the current variables in the context
  previousVars <- lift $ UnifyCtx.getVarsSoFar uvarCtx
  
  -- Perform the insert operation
  lift $ UnifyCtx.insert uvarCtx x pty
  
  -- If the variable was not already present, log the event
  case Map.lookup x previousVars of
    Just _ => do
      pure ()
    Nothing => do
      modify (\events => (Added uvarCtx x) :: events)

-- Logs a 'Closed' event if the context was not previously closed.
public export
close
   : Monad m
  => UVarCtx
  -> UnifyCtxWithLogT m ()
close uvarCtx = MkUnifyCtxWithLogT $ do
  -- Check if the context is already closed
  wasClosed <- lift $ UnifyCtx.isClosedUVarCtx uvarCtx
  
  -- Perform the close operation
  lift $ UnifyCtx.close uvarCtx
  
  -- If the context was not already closed, log the close event
  unless wasClosed $ do
    modify (\events => (Closed uvarCtx) :: events)

----------------------------------------

public export
implementation Show UnifyCtxEvent where
  showPrec p (Added (MkNode i) var)
    = showParens (p /= Open)
    $ "Added (MkNode " ++ show i ++ ") " ++ showPrec App var
  showPrec p (Closed (MkNode i))
    = showParens (p /= Open)
    $ "Closed (MkNode " ++ show i ++ ")"

public export
implementation Eq UnifyCtxEvent where
  Added node1 var1 == Added node2 var2
    = node1 == node2 && var1 == var2
  Closed node1 == Closed node2
    = node1 == node2
  _ == _
    = False

----------------------------------------

public export
runTest
   : UnifyCtx (UnifyCtxWithLog a)
  -> Either UnifyCtxError (List UnifyCtxEvent, a)
runTest body = do
  runUnifyCtxWithoutGeneralizing $ do
    secondPhase <- body
    runStateT [] $ do
      runUnifyCtxWithLog secondPhase

execTest
   : UnifyCtx (UnifyCtxWithLog ())
  -> Either UnifyCtxError (List UnifyCtxEvent)
execTest body = do
  runUnifyCtxWithoutGeneralizing $ do
    secondPhase <- body
    execStateT [] $ do
      runUnifyCtxWithLog secondPhase

example1 : UnifyCtx (UnifyCtxWithLog ())
example1 = do
  uvarTy <- liftUnifyTy newUVarTy
  uvarCtx <- newUVarCtx  
  pure $ do
    -- Insert a new variable (should be logged)
    insert uvarCtx "x" uvarTy
    
    -- Insert the same variable again (should not be logged)
    insert uvarCtx "x" uvarTy
    
    -- Insert another new variable (should be logged)
    insert uvarCtx "y" uvarTy
    
    -- Close the context (should be logged)
    close uvarCtx
    
    -- Close the context again (should not be logged)
    close uvarCtx

public export
test1 : IO ()
test1 = printLn ( execTest example1
               == Right
                    [ Closed (MkNode 0)
                    , Added (MkNode 0) "y"
                    , Added (MkNode 0) "x"
                    ]
                )

example2 : UnifyCtx (UnifyCtxWithLog ())
example2 = do
  uvarTy <- liftUnifyTy newUVarTy
  uvarCtx <- newUVarCtx  
  pure $ do
    close uvarCtx
    
    -- insert after close is not allowed
    insert uvarCtx "x" uvarTy

public export
test2 : IO ()
test2 = printLn ( execTest example2
               == Left (ContextCannotHaveVariable (MkNode 0) "x")
                )
