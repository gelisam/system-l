-- "UnifyCtx" stands for "Unification for Contexts". A Context is a Map from
-- variable name to Ty. In the unification algorithm, we want to figure out
-- which variables are part of the context and which types they have, so we use
-- PContext, a "Partial Context" which maps each variable name to a PTy a
-- "Partial Type". As we learn more information about each PTy, more and more of
-- its unification variables (UVarTy) get assigned a concrete type. Similarly,
-- as we learn more information about which variables are in the context,
-- 'varsSoFar' gets filled with more and more variables. It is also possible to
-- no longer be uncertain about which variables are in the context, at which
-- point we 'close' the PContext in order to indicate that no more variables can
-- be added.
--
-- The only constraint which can be expressed in UnifyCtx is that two contexts
-- are equal, via 'unifyUVarCtxs'. The "UnifyCtxWithConstraints" module makes it
-- possible to express more complicated constraints, e.g. that two contexts
-- should be disjoint.
module UTerm.UnifyCtx

import Control.Monad.State
import Data.SortedMap as Map
import Data.SortedSet as Set

import Ty
import UTerm.ObserveCtx
import UTerm.PolyTy
import UTerm.PTy
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.ExceptT
import Util.Map as Map
import Util.MapT
import Util.These

----------------------------------------

public export
data UnifyCtxError
  = VariableAddedToClosedContext String UVarCtx
  | UnifyTyError UnifyTyError

Impl : (Type -> Type) -> Type -> Type
Impl m = ExceptT UnifyCtxError (UnionFindT PContext (UnifyTyT m))

export
record UnifyCtxT (m : Type -> Type) (a : Type) where
  constructor MkUnifyCtxT
  unUnifyCtxT : Impl m a

public export
UnifyCtx : Type -> Type
UnifyCtx = UnifyCtxT Identity

public export
runUnifyCtxTWithoutGeneralizing
   : Monad m
  => UnifyCtxT m a
  -> m (Either UnifyCtxError a)
runUnifyCtxTWithoutGeneralizing (MkUnifyCtxT body) = do
  (runUnifyTyTWithoutGeneralizing $ runUnionFindT $ runExceptT body) >>= \case
    Left unifyTyError => do
      pure $ Left $ UnifyTyError unifyTyError
    Right (Left unifyCtxError) => do
      pure $ Left unifyCtxError
    Right (Right a) => do
      pure $ Right a

public export
runUnifyCtxWithoutGeneralizing
   : UnifyCtx a
  -> Either UnifyCtxError a
runUnifyCtxWithoutGeneralizing
  = runIdentity . runUnifyCtxTWithoutGeneralizing

----------------------------------------

public export
implementation Monad m => Functor (UnifyCtxT m) where
  map f (MkUnifyCtxT body) = MkUnifyCtxT $ map f body

public export
implementation Monad m => Applicative (UnifyCtxT m) where
  pure x = MkUnifyCtxT $ pure x
  (MkUnifyCtxT f) <*> (MkUnifyCtxT x) = MkUnifyCtxT (f <*> x)

public export
implementation Monad m => Monad (UnifyCtxT m) where
  (MkUnifyCtxT ma) >>= f
    = MkUnifyCtxT (ma >>= \a => unUnifyCtxT (f a))

public export
implementation MonadTrans UnifyCtxT where
  lift = MkUnifyCtxT . lift . lift . lift

public export
implementation MapT UnifyCtxT where
  mapT f (MkUnifyCtxT body) = MkUnifyCtxT (mapT (mapT (mapT f)) body)

-- Note that UnifyCtxT discharges the MonadUnifyTy constraint, it does _not_
-- delegate to the m. Being able to unify type variables is an important part of
-- UnifyCtxT's API.
public export
implementation Monad m => MonadUnifyTy (UnifyCtxT m) where
  liftUnifyTy body = MkUnifyCtxT (go body)
    where
      go : UnifyTy a -> Impl m a
      go body = do
        let body' : UnifyTyT m a
            body' = liftUnifyTy body
        lift $ lift body'

-- UnifyCtxT also discharges the MonadObserveCtx constraint. Being able to
-- observe the contexts is another important part of UnifyCtxT's API.
public export
implementation Monad m => MonadObserveCtx (UnifyCtxT m) where
  liftObserveCtx body = MkUnifyCtxT $ do
    let action : UnionFindT PContext UnifyTy a
        action = runObserveCtx body
    let f : Identity x -> m x
        f (Id x) = pure x
    let actionT : UnionFindT PContext (UnifyTyT m) a
        actionT = mapT (mapT f) action
    lift actionT

----------------------------------------

public export
newUVarCtxImpl : Monad m => Impl m UVarCtx
newUVarCtxImpl = do
  liftUnionFind $ newNode $ Just $ MkPContext
    { varsSoFar
        = Map.empty
    , closed
        = False
    }

getPContextImpl
   : Monad m
  => UVarCtx
  -> Impl m PContext
getPContextImpl node = do
  (liftUnionFind $ getValue node) >>= \case
    Nothing => do
      -- This module's API never stores Nothing, but to make the typechecker
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

insertImpl
   : Monad m
  => UVarCtx
  -> String
  -> PTy
  -> Impl m ()
insertImpl uvarCtx x pty = do
  MkPContext varsSoFar closed <- getPContextImpl uvarCtx

  case Map.lookup x varsSoFar of
    Just existingPty => do
      -- Variable already present; unify the old and new types
      liftUnifyTy $ unifyPTys existingPty pty
    Nothing => do
      -- Can't add new variable if the context is closed
      when closed $ do
        throwE $ VariableAddedToClosedContext x uvarCtx

      -- We can add the new variable
      liftUnionFind $ setValue uvarCtx $ Just $ MkPContext
        { varsSoFar = Map.insert x pty varsSoFar
        , closed = closed
        }

closeImpl
   : Monad m
  => UVarCtx
  -> Impl m ()
closeImpl uvarCtx = do
  MkPContext varsSoFar _ <- getPContextImpl uvarCtx

  -- Set closed flag to True
  liftUnionFind $ setValue uvarCtx $ Just $ MkPContext
    { varsSoFar = varsSoFar
    , closed = True
    }

public export
unifyUVarCtxsImpl
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> Impl m ()
unifyUVarCtxsImpl uvarCtx1 uvarCtx2 = do
  -- Get the context information for both contexts
  MkPContext varsSoFar1 closed1 <- getPContextImpl uvarCtx1
  MkPContext varsSoFar2 closed2 <- getPContextImpl uvarCtx2

  -- Make both vars share the same underlying node in the union-find.
  -- Start with the variables from pcontext1 and add the variables from
  -- pcontext2, so that the union contains the variables from both.
  let pcontext1 = MkPContext varsSoFar1 closed1
  liftUnionFind $ union uvarCtx1 uvarCtx2 $ Just pcontext1
  for_ (Map.toList varsSoFar2) $ \(x, pty2) => do
    insertImpl uvarCtx1 x pty2

  -- If either context is closed, then their union cannot accept more variables,
  -- as that would cause that closed context to accept more variables.
  when (closed1 || closed2) $ do
    closeImpl uvarCtx1

public export
showUnifyCtxError : UnifyCtxError -> String
showUnifyCtxError (VariableAddedToClosedContext var (MkNode i)) =
  "Context ??" ++ show i ++ " cannot have variable " ++ show var
showUnifyCtxError (UnifyTyError e) =
  showUnifyTyError e

----------------------------------------

public export
interface (MonadUnifyTy m, MonadObserveCtx m) => MonadUnifyCtx m where
  -- Creates a new open context (allows adding more variables).
  newUVarCtx
    : m UVarCtx

  -- Similar to Map.insert. Fails if the context is closed.
  insert
    : UVarCtx -> String -> PTy -> m ()

  -- Closes a context, preventing further variables from being added.
  close
    : UVarCtx -> m ()
  
  -- Unifies two contexts, merging their variables and types. Fails if that
  -- would add variables to a closed context.
  unifyUVarCtxs
    : UVarCtx -> UVarCtx -> m ()

-- Creates an open context with initial variables.
-- More variables can be added later.
public export
newOpenUVarCtx
   : MonadUnifyCtx m
  => Map String PTy
  -> m UVarCtx
newOpenUVarCtx vars = do
  uvarCtx <- newUVarCtx
  for_ (Map.toList vars) $ \(x, pty) => do
    insert uvarCtx x pty
  pure uvarCtx

-- Creates a closed context with exactly the specified variables.
-- No more variables can be added later.
public export
newClosedUVarCtx
   : MonadUnifyCtx m
  => Map String PTy
  -> m UVarCtx
newClosedUVarCtx vars = do
  uvarCtx <- newOpenUVarCtx vars
  close uvarCtx
  pure uvarCtx

public export
implementation Monad m => MonadUnifyCtx (UnifyCtxT m) where
  newUVarCtx = MkUnifyCtxT $ do
    newUVarCtxImpl
  insert uvarCtx x pty = MkUnifyCtxT $ do
    insertImpl uvarCtx x pty
  close uvarCtx = MkUnifyCtxT $ do
    closeImpl uvarCtx
  unifyUVarCtxs uvarCtx1 uvarCtx2 = MkUnifyCtxT $ do
    unifyUVarCtxsImpl uvarCtx1 uvarCtx2

public export
implementation MonadUnifyCtx m => MonadUnifyCtx (StateT s m) where
  newUVarCtx
    = lift newUVarCtx
  insert uvarCtx x pty
    = lift $ insert uvarCtx x pty
  close uvarCtx
    = lift $ close uvarCtx
  unifyUVarCtxs uvarCtx1 uvarCtx2
    = lift $ unifyUVarCtxs uvarCtx1 uvarCtx2

public export
implementation MonadUnifyCtx m => MonadUnifyCtx (ExceptT e m) where
  newUVarCtx
    = lift newUVarCtx
  insert uvarCtx x pty
    = lift $ insert uvarCtx x pty
  close uvarCtx
    = lift $ close uvarCtx
  unifyUVarCtxs uvarCtx1 uvarCtx2
    = lift $ unifyUVarCtxs uvarCtx1 uvarCtx2

----------------------------------------

public export
implementation Show UnifyCtxError where
  showPrec p (VariableAddedToClosedContext var (MkNode i))
    = showParens (p /= Open)
    $ "VariableAddedToClosedContext " ++ showPrec App var ++ " (MkNode " ++ show i ++ ")"
  showPrec p (UnifyTyError e)
    = showParens (p /= Open)
    $ "UnifyTyError " ++ showPrec App e

public export
implementation Eq UnifyCtxError where
  VariableAddedToClosedContext var1 node1 == VariableAddedToClosedContext var2 node2
    = node1 == node2 && var1 == var2
  UnifyTyError e1 == UnifyTyError e2
    = e1 == e2
  _ == _
    = False

----------------------------------------

example1 : UnifyCtx (Map String PTy, Map String PTy, Map String PTy, Map String PTy)
example1 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarTy3 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy0 uvarTy1)
    , ("y", uvarTy2)
    ]
  uvarCtx2 <- newUVarCtx
  uvarCtx3 <- newOpenUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy1 uvarTy2)
    , ("z", uvarTy3)
    ]
  uvarCtx4 <- newOpenUVarCtx $ Map.fromList
    [ ("x", PTen uvarTy2 uvarTy3)
    , ("y", uvarTy2)
    , ("xyz", uvarTy3)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2
  unifyUVarCtxs uvarCtx2 uvarCtx3

  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  vars3 <- liftObserveCtx $ zonkUVarCtx uvarCtx3
  vars4 <- liftObserveCtx $ zonkUVarCtx uvarCtx4
  pure (vars1, vars2, vars3, vars4)

-- The algorithm doesn't guarantee which variable is chosen as the root (see
-- UnifyTy.test1).
public export
test1 : IO ()
test1 = printLn ( runUnifyCtxWithoutGeneralizing example1
               == Right
                    ( Map.fromList
                        [ ("x", PImp (UVarTy (MkNode 0)) (UVarTy (MkNode 0)))
                        , ("y", UVarTy (MkNode 0))
                        , ("z", UVarTy (MkNode 3))
                        ]
                    , Map.fromList
                        [ ("x", PImp (UVarTy (MkNode 0)) (UVarTy (MkNode 0)))
                        , ("y", UVarTy (MkNode 0))
                        , ("z", UVarTy (MkNode 3))
                        ]
                    , Map.fromList
                        [ ("x", PImp (UVarTy (MkNode 0)) (UVarTy (MkNode 0)))
                        , ("y", UVarTy (MkNode 0))
                        , ("z", UVarTy (MkNode 3))
                        ]
                    , Map.fromList
                        [ ("x", PTen (UVarTy (MkNode 0)) (UVarTy (MkNode 3)))
                        , ("y", UVarTy (MkNode 0))
                        , ("xyz", UVarTy (MkNode 3))
                        ]
                    )
                )

example2 : UnifyCtx (Map String PTy, Map String PTy)
example2 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]
  uvarCtx2 <- newClosedUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    , ("y", uvarTy0)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure (vars1, vars2)

public export
test2 : IO ()
test2 = printLn ( runUnifyCtxWithoutGeneralizing example2
               == Right
                    ( Map.fromList
                        [ ("x", UVarTy (MkNode 0))
                        , ("y", UVarTy (MkNode 0))
                        ]
                    , Map.fromList
                        [ ("x", UVarTy (MkNode 0))
                        , ("y", UVarTy (MkNode 0))
                        ]
                    )
                )

example3 : UnifyCtx ()
example3 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newClosedUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]
  uvarCtx2 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    , ("y", uvarTy0)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

public export
test3 : IO ()
test3 = printLn ( runUnifyCtxWithoutGeneralizing example3
               == ( Left
                  $ VariableAddedToClosedContext "y" (MkNode 0)
                  )
                )

example4 : UnifyCtx ()
example4 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarTy3 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy0 uvarTy1)
    , ("y", uvarTy3)
    ]
  uvarCtx2 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy3)
    , ("y", PPar uvarTy1 uvarTy2)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

public export
test4 : IO ()
test4 = printLn ( runUnifyCtxWithoutGeneralizing example4
               == ( Left
                  $ UnifyTyError
                  $ TypeMismatch
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 1)))
                      (ParF (UVarTy (MkNode 1)) (UVarTy (MkNode 2)))
                  )
                )

example5 : UnifyCtx (Map String PTy, Map String PTy)
example5 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy0 uvarTy1)
    , ("y", uvarTy0)
    ]
  uvarCtx2 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy2)
    , ("y", uvarTy2)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

  vars1 <- liftObserveCtx $ zonkDepthUVarCtx 3 uvarCtx1
  vars2 <- liftObserveCtx $ zonkDepthUVarCtx 3 uvarCtx2
  pure (vars1, vars2)

public export
test5 : IO ()
test5 = printLn ( runUnifyCtxWithoutGeneralizing example5
               == ( Left
                  $ UnifyTyError
                  $ OccursCheckFailed
                      (MkNode 0)
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 1)))
                  )
                )

public export
example6 : UnifyCtx Bool
example6 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]
  uvarCtx2 <- newClosedUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]

  -- Unify an open context with a closed context
  unifyUVarCtxs uvarCtx1 uvarCtx2

  -- Check if the result is closed
  liftObserveCtx $ isClosedUVarCtx uvarCtx1

public export
test6 : IO ()
test6 = printLn ( runUnifyCtxWithoutGeneralizing example6
               == Right True
                )

public export
example7 : UnifyCtx ()
example7 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy

  -- Create an open context with one variable
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]

  -- Create a closed context with one variable
  uvarCtx2 <- newClosedUVarCtx $ Map.fromList
    [ ("x", uvarTy0)
    ]

  -- Unify the open context with the closed context
  unifyUVarCtxs uvarCtx1 uvarCtx2

  -- Now try to add a new variable "y" to the unified context
  -- With the bug (closed1 && closed2), this would succeed incorrectly
  -- With the fix (closed1 || closed2), this should fail
  uvarCtx3 <- newOpenUVarCtx $ Map.fromList
    [ ("y", uvarTy1)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx3

public export
test7 : IO ()
test7 = printLn ( runUnifyCtxWithoutGeneralizing example7
               == ( Left
                  $ VariableAddedToClosedContext "y" (MkNode 0)
                  )
                )
