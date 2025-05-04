module UTerm.UnifyCtx

import Control.Monad.State
import Data.SortedMap as Map
import Data.SortedSet as Set

import Ty
import UTerm.PolyTy
import UTerm.PTy
import UTerm.UnifyExtensible
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.ExceptT
import Util.Map as Map
import Util.These

----------------------------------------

public export
record PContext where
  constructor MkPContext
  varsSoFar
     : Map String PTy
  moreVarsAllowed
     : UVarExtensible

public export
UVarCtx : Type
UVarCtx = Node PContext

public export
data UnifyCtxError
  = ContextCannotHaveVariable UVarCtx String
  | UnifyTyError UnifyTyError

Impl : (Type -> Type) -> Type -> Type
Impl m = ExceptT UnifyCtxError (UnionFindT PContext (UnifyExtensibleT (UnifyTyT m)))

public export
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
  (runUnifyTyTWithoutGeneralizing $ runUnifyExtensibleT $ runUnionFindT $ runExceptT body) >>= \case
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

-----------------------------------------

public export
implementation Monad m => Functor (UnifyCtxT m) where
  map f (MkUnifyCtxT m) = MkUnifyCtxT $ map f m

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
  lift = MkUnifyCtxT . lift . lift . lift . lift

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
        lift $ lift $ lift body'

-----------------------------------------

-- Could contain any number of variables.
public export
newUVarCtx : Monad m => UnifyCtxT m UVarCtx
newUVarCtx = MkUnifyCtxT $ do
  uvarExtensible <- liftUnifyExtensible newExtensibleUVar
  liftUnionFind $ newNode $ Just $ MkPContext
    { varsSoFar
        = Map.empty
    , moreVarsAllowed
        = uvarExtensible
    }

-- Must contain at least the specified variables.
public export
newExtensibleUVarCtx : Monad m => Map String PTy -> UnifyCtxT m UVarCtx
newExtensibleUVarCtx vars = MkUnifyCtxT $ do
  uvarExtensible <- liftUnifyExtensible newExtensibleUVar
  liftUnionFind $ newNode $ Just $ MkPContext
    { varsSoFar
        = vars
    , moreVarsAllowed
        = uvarExtensible
    }

-- Must contain exactly the specified variables.
public export
newNonExtensibleUVarCtx : Monad m => Map String PTy -> UnifyCtxT m UVarCtx
newNonExtensibleUVarCtx vars = MkUnifyCtxT $ do
  liftUnionFind $ newNode $ Just $ MkPContext
    { varsSoFar
        = vars
    , moreVarsAllowed
        = nonExtensibleUVar
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
        , moreVarsAllowed
            = nonExtensibleUVar
        }
    Just pctx => do
      pure pctx

public export
unifyUVarCtxs
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> UnifyCtxT m ()
unifyUVarCtxs uvarCtx1 uvarCtx2 = MkUnifyCtxT $ do
  MkPContext varsSoFar1 moreVarsAllowed1 <- getPContextImpl uvarCtx1
  MkPContext varsSoFar2 moreVarsAllowed2 <- getPContextImpl uvarCtx2

  isExtensible1 <- liftUnifyExtensible $ getIsExtensible moreVarsAllowed1
  isExtensible2 <- liftUnifyExtensible $ getIsExtensible moreVarsAllowed2
  liftUnifyExtensible $ unifyUVarExtensibles moreVarsAllowed1 moreVarsAllowed2

  varsSoFar3 <- sequence $ Map.withKey $ Map.union varsSoFar1 varsSoFar2 $ \case
    This pty1 => \x => do
      -- This variable from varsSoFar1 is being added to varsSoFar2, is that
      -- allowed?
      case isExtensible2 of
        False => do
          throwE $ ContextCannotHaveVariable uvarCtx2 x
        True => do
          pure pty1
    That pty2 => \x => do
      -- This variable from varsSoFar2 is being added to varsSoFar1, is that
      -- allowed?
      case isExtensible1 of
        False => do
          throwE $ ContextCannotHaveVariable uvarCtx1 x
        True => do
          pure pty2
    Both pty1 pty2 => \_ => do
      liftUnifyTy $ unifyPTys pty1 pty2
      pure pty1
  
  liftUnionFind $ union uvarCtx1 uvarCtx2 $ Just $ MkPContext
    { varsSoFar
        = varsSoFar3
    , moreVarsAllowed
        = moreVarsAllowed1
    }

public export
zonkUVarCtx : Monad m => UVarCtx -> UnifyCtxT m (Map String PTy)
zonkUVarCtx uvarCtx = MkUnifyCtxT $ do
  MkPContext varsSoFar_ _ <- getPContextImpl uvarCtx
  for varsSoFar_ $ \pty => do
    liftUnifyTy $ zonkPTy pty

public export
zonkDepthUVarCtx : Monad m => Nat -> UVarCtx -> UnifyCtxT m (Map String PTy)
zonkDepthUVarCtx depth uvarCtx = MkUnifyCtxT $ do
  MkPContext varsSoFar_ _ <- getPContextImpl uvarCtx
  for varsSoFar_ $ \pty => do
    liftUnifyTy $ zonkDepthPTy depth pty

----------------------------------------

public export
showUnifyCtxError : UnifyCtxError -> String
showUnifyCtxError (ContextCannotHaveVariable (MkNode i) var) =
  "Context ??" ++ show i ++ " cannot have variable " ++ show var
showUnifyCtxError (UnifyTyError e) =
  showUnifyTyError e

----------------------------------------

public export
implementation Show UnifyCtxError where
  showPrec p (ContextCannotHaveVariable (MkNode i) var)
    = showParens (p /= Open)
    $ "ContextCannotHaveVariable (MkNode " ++ show i ++ ") " ++ showPrec App var
  showPrec p (UnifyTyError e)
    = showParens (p /= Open)
    $ "UnifyTyError " ++ showPrec App e

public export
implementation Eq UnifyCtxError where
  ContextCannotHaveVariable node1 var1 == ContextCannotHaveVariable node2 var2
    = node1 == node2 && var1 == var2
  UnifyTyError e1 == UnifyTyError e2
    = e1 == e2
  _ == _
    = False

----------------------------------------

example1 : UnifyCtx (Map String PTy, Map String PTy, Map String PTy, Map String PTy)
example1 = do
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarTy3 <- liftUnifyTy newUVarTy
  uvarTy4 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy1 uvarTy2)
    , ("y", uvarTy3)
    ]
  uvarCtx2 <- newUVarCtx
  uvarCtx3 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy2 uvarTy3)
    , ("z", uvarTy4)
    ]
  uvarCtx4 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", PTen uvarTy3 uvarTy4)
    , ("y", uvarTy3)
    , ("xyz", uvarTy4)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2
  unifyUVarCtxs uvarCtx2 uvarCtx3

  vars1 <- zonkUVarCtx uvarCtx1
  vars2 <- zonkUVarCtx uvarCtx2
  vars3 <- zonkUVarCtx uvarCtx3
  vars4 <- zonkUVarCtx uvarCtx4
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
  uvarTy <- liftUnifyTy newUVarTy
  uvarCtx1 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy)
    ]
  uvarCtx2 <- newNonExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy)
    , ("y", uvarTy)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

  vars1 <- zonkUVarCtx uvarCtx1
  vars2 <- zonkUVarCtx uvarCtx2
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
  uvarTy <- liftUnifyTy newUVarTy
  uvarCtx1 <- newNonExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy)
    ]
  uvarCtx2 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy)
    , ("y", uvarTy)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

public export
test3 : IO ()
test3 = printLn ( runUnifyCtxWithoutGeneralizing example3
               == ( Left
                  $ ContextCannotHaveVariable (MkNode 0) "y"
                  )
                )

example4 : UnifyCtx ()
example4 = do
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarTy3 <- liftUnifyTy newUVarTy
  uvarTy4 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy1 uvarTy2)
    , ("y", uvarTy4)
    ]
  uvarCtx2 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy4)
    , ("y", PPar uvarTy2 uvarTy3)
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
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy
  uvarTy3 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", PImp uvarTy1 uvarTy2)
    , ("y", uvarTy1)
    ]
  uvarCtx2 <- newExtensibleUVarCtx $ Map.fromList
    [ ("x", uvarTy3)
    , ("y", uvarTy3)
    ]

  unifyUVarCtxs uvarCtx1 uvarCtx2

  vars1 <- zonkDepthUVarCtx 3 uvarCtx1
  vars2 <- zonkDepthUVarCtx 3 uvarCtx2
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

----------------------------------------

public export
interface Monad m => MonadUnifyCtx m where
  liftUnifyCtx : UnifyCtx a -> m a

public export
implementation Monad m => MonadUnifyCtx (UnifyCtxT m) where
  liftUnifyCtx body = MkUnifyCtxT $ go body
    where
      go : UnifyCtx a -> Impl m a
      go body = do
        let body' = runUnifyCtxWithoutGeneralizing body
        case body' of
          Left e => throwE e
          Right a => pure a

public export
implementation MonadUnifyCtx m => MonadUnifyCtx (StateT s m) where
  liftUnifyCtx body = lift $ liftUnifyCtx body

public export
implementation MonadUnifyCtx m => MonadUnifyCtx (ExceptT e m) where
  liftUnifyCtx body = lift $ liftUnifyCtx body
