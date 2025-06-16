-- "UnifyTy" stands for "Unification for Types". This module can unify two
-- PTy's, figuring out which Ty the unification variables at matching positions
-- must refer to and detecting contradictions. The module "Infer.idr" uses this
-- when traversing a UTerm to make sure that two types which are supposed to be
-- equal according to the typing rules really are equal.
module UTerm.UnifyTy

import Control.Monad.Reader
import Control.Monad.State

import Ty
import UTerm.PTy
import UTerm.UnionFind
import Util.Depth
import Util.ExceptT
import Util.MapT

----------------------------------------

public export
data UnifyTyError
  = OccursCheckFailed (Root CTy) CTy
  | TypeMismatch CTy CTy

Impl : (Type -> Type) -> Type -> Type
Impl m = ExceptT UnifyTyError (UnionFindT CTy m)

export
record UnifyTyT (m : Type -> Type) (a : Type) where
  constructor MkUnifyTyT
  unUnifyTyT : Impl m a

public export
UnifyTy : Type -> Type
UnifyTy = UnifyTyT Identity

-- runUnifyTy is defined in "GeneralizeTy.idr". Outside of this module, the most
-- common way to use UnifyTy is to calculate a partial value like a PTy which
-- contains unification variables, and to generalize the value by replacing
-- those unification variables with quantified variables.
public export
runUnifyTyTWithoutGeneralizing
   : Monad m
  => UnifyTyT m a
  -> m (Either UnifyTyError a)
runUnifyTyTWithoutGeneralizing (MkUnifyTyT body) = runUnionFindT (runExceptT body)

public export
runUnifyTyWithoutGeneralizing
   : UnifyTy a
  -> Either UnifyTyError a
runUnifyTyWithoutGeneralizing = runIdentity . runUnifyTyTWithoutGeneralizing

-----------------------------------------

public export
implementation Monad m => Functor (UnifyTyT m) where
  map f (MkUnifyTyT body) = MkUnifyTyT $ map f body

public export
implementation Monad m => Applicative (UnifyTyT m) where
  pure x = MkUnifyTyT $ pure x
  (MkUnifyTyT f) <*> (MkUnifyTyT x) = MkUnifyTyT $ f <*> x

public export
implementation Monad m => Monad (UnifyTyT m) where
  (MkUnifyTyT ma) >>= f
    = MkUnifyTyT (ma >>= \a => unUnifyTyT (f a))

public export
implementation MonadTrans UnifyTyT where
  lift = MkUnifyTyT . lift . lift

public export
implementation MapT UnifyTyT where
  mapT f (MkUnifyTyT body) = MkUnifyTyT (mapT (mapT f) body)

public export
implementation MonadUnionFind v m => MonadUnionFind v (UnifyTyT m) where
  liftUnionFind = lift . liftUnionFind

-----------------------------------------

public export
newUVarTy : Monad m => UnifyTyT m PTy
newUVarTy = MkUnifyTyT $ do
  node <- lift $ newNode Nothing
  pure $ UVarTy node

occursCheckImpl
   : Monad m
  => Node CTy
  -> CTy
  -> Impl m ()
occursCheckImpl needleNode cty = do
  root <- lift $ findRoot needleNode
  bools <- traverse (rootOccursInPTy root) cty
  if any id bools
    then throwE $ OccursCheckFailed root cty
    else pure ()
  where
    rootOccursInPTy
       : Root CTy
      -> PTy
      -> Impl m Bool
    rootOccursInPTy needleRoot pty = do
      let go : PTy -> Impl m Bool
          go (UVarTy node) = do
            root <- lift $ findRoot node
            pure (root == needleRoot)
          go (Ctor cty) = do
            bools <- traverse go cty
            pure $ any id bools
      go pty

public export
zonkImpl
   : Monad m
  => Depth
  -> PTy
  -> Impl m PTy
zonkImpl (Finite Z) pty = do
  pure pty
zonkImpl depth (UVarTy node) = do
  root <- lift $ findRoot node
  (lift $ getValue root) >>= \case
    Nothing =>
      pure $ UVarTy root
    Just cty => do
      cty' <- traverse (zonkImpl (decrDepth depth)) cty
      pure $ Ctor cty'
zonkImpl depth (Ctor cty) = do
  cty' <- traverse (zonkImpl (decrDepth depth)) cty
  pure $ Ctor cty'

public export
zonkPTy : Monad m => PTy -> UnifyTyT m PTy
zonkPTy pty = MkUnifyTyT $ do
  zonkImpl Infinite pty

public export
zonkDepthPTy : Monad m => Nat -> PTy -> UnifyTyT m PTy
zonkDepthPTy depth pty = MkUnifyTyT $ do
  zonkImpl (Finite depth) pty

mutual
  unifyUVarTysImpl
     : Monad m
    => Node CTy
    -> Node CTy
    -> Impl m ()
  unifyUVarTysImpl node1 node2 = do
    root1 <- lift $ findRoot node1
    root2 <- lift $ findRoot node2
    if root1 == root2
      then pure ()
      else do
        maybeV1 <- lift $ getValue root1
        maybeV2 <- lift $ getValue root2
        case (maybeV1, maybeV2) of
          (Nothing, Nothing) => do
            lift $ union root1 root2 Nothing
          (Just cty1, Nothing) => do
            occursCheckImpl root2 cty1
            lift $ union root1 root2 (Just cty1)
          (Nothing, Just cty2) => do
            occursCheckImpl root1 cty2
            lift $ union root1 root2 (Just cty2)
          (Just cty1, Just cty2) => do
            occursCheckImpl root1 cty2
            occursCheckImpl root2 cty1
            unifyCTysImpl cty1 cty2
            lift $ union root1 root2 (Just cty1)

  unifyUVarTyWithCtyImpl
     : Monad m
    => Node CTy
    -> CTy
    -> Impl m ()
  unifyUVarTyWithCtyImpl node1 cty2 = do
    root1 <- lift $ findRoot node1
    (lift $ getValue root1) >>= \case
      Nothing => do
        occursCheckImpl root1 cty2
        lift $ setValue root1 $ Just cty2
      Just cty1 =>
        unifyCTysImpl cty1 cty2

  unifyPTysImpl
     : Monad m
    => PTy
    -> PTy
    -> Impl m ()
  unifyPTysImpl (UVarTy node1) (UVarTy node2) =
    unifyUVarTysImpl node1 node2
  unifyPTysImpl (UVarTy node) (Ctor cty) =
    unifyUVarTyWithCtyImpl node cty
  unifyPTysImpl (Ctor cty) (UVarTy node) =
    unifyUVarTyWithCtyImpl node cty
  unifyPTysImpl (Ctor cty1) (Ctor cty2) =
    unifyCTysImpl cty1 cty2

  unifyCTysImpl
     : Monad m
    => CTy
    -> CTy
    -> Impl m ()
  unifyCTysImpl (ImpF a1 b1) (ImpF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (MinusF a1 b1) (MinusF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (TenF a1 b1) (TenF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (SumF a1 b1) (SumF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (WithF a1 b1) (WithF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (ParF a1 b1) (ParF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl cty1 cty2 = do
    throwE (TypeMismatch cty1 cty2)

public export
unifyPTys : Monad m => PTy -> PTy -> UnifyTyT m ()
unifyPTys pty1 pty2 = MkUnifyTyT $ do
  unifyPTysImpl pty1 pty2

public export
showUnifyTyError : UnifyTyError -> String
showUnifyTyError (OccursCheckFailed (MkNode i) pty) =
  "Occurs check failed: Node ?" ++ show i ++ " occurs in " ++ showPrec App pty
showUnifyTyError (TypeMismatch cty1 cty2) =
  "Type mismatch: Cannot unify " ++ showPrec App cty1 ++ " with " ++ showPrec App cty2

----------------------------------------

public export
implementation Show UnifyTyError where
  showPrec p (OccursCheckFailed (MkNode i) pty)
    = showParens (p /= Open)
    $ "OccursCheckFailed (MkNode " ++ show i ++ ") " ++ showPrec App pty
  showPrec p (TypeMismatch cty1 cty2)
    = showParens (p /= Open)
    $ "TypeMismatch " ++ showPrec App cty1 ++ " " ++ showPrec App cty2

public export
implementation Eq UnifyTyError where
  OccursCheckFailed node1 pty1 == OccursCheckFailed node2 pty2
    = node1 == node2
   && pty1 == pty2
  TypeMismatch cty1 cty2 == TypeMismatch cty3 cty4
    = cty1 == cty3
   && cty2 == cty4
  _ == _
    = False

----------------------------------------

example1 : UnifyTy PTy
example1 = do
  uvar0 <- newUVarTy
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy
  uvar3 <- newUVarTy
  unifyPTys (PImp uvar0 uvar1) (PImp uvar1 uvar2)
  zonkPTy $ PImp uvar0 $ PImp uvar1 $ PImp uvar2 uvar3

-- The algorithm doesn't guarantee which variable is chosen as the root, so what
-- I really want to test is that there are two distinct nodes n1 and n2 such
-- that the result is
--
--   Right $ PImp n1 $ PImp n1 $ PImp n1 n2
--
-- But it is much easier to just inspect the result and use the roots 0 and 3
-- which happen to be chosen by the algorithm and use that as the test case.
public export
test1 : IO ()
test1 = printLn ( runUnifyTyWithoutGeneralizing example1
               == ( Right
                  $ PImp (UVarTy (MkNode 0))
                  $ PImp (UVarTy (MkNode 0))
                  $ PImp (UVarTy (MkNode 0)) (UVarTy (MkNode 3))
                  )
                )

example2 : UnifyTy ()
example2 = do
  uvar0 <- newUVarTy
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy

  unifyPTys (PImp uvar0 uvar1) (PPar uvar1 uvar2)

public export
test2 : IO ()
test2 = printLn ( runUnifyTyWithoutGeneralizing example2
               == ( Left
                  $ TypeMismatch
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 1)))
                      (ParF (UVarTy (MkNode 1)) (UVarTy (MkNode 2)))
                  )
                )

example3 : UnifyTy (PTy, PTy)
example3 = do
  uvar0 <- newUVarTy
  uvar1 <- newUVarTy

  unifyPTys uvar0 (PImp uvar0 uvar1)

  pty1 <- zonkDepthPTy 3 uvar0
  pty2 <- zonkDepthPTy 3 uvar1
  pure (pty1, pty2)


public export
test3 : IO ()
test3 = printLn ( runUnifyTyWithoutGeneralizing example3
               == ( Left
                  $ OccursCheckFailed
                      (MkNode 0)
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 1)))
                  )
                )


example4 : UnifyTy (PTy, PTy, PTy)
example4 = do
  uvar0 <- newUVarTy
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy

  unifyPTys (PImp uvar0 uvar1) uvar2
  unifyPTys uvar0 uvar2

  pty1 <- zonkDepthPTy 3 uvar0
  pty2 <- zonkDepthPTy 3 uvar1
  pty3 <- zonkDepthPTy 3 uvar2
  pure (pty1, pty2, pty3)


public export
test4 : IO ()
test4 = printLn ( runUnifyTyWithoutGeneralizing example4
               == ( Left
                  $ OccursCheckFailed
                      (MkNode 0)
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 1)))
                  )
                )

example5 : UnifyTy (PTy, PTy)
example5 = do
  uvar0 <- newUVarTy
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy

  unifyPTys uvar0 (PImp uvar1 uvar2)
  unifyPTys uvar1 (PImp uvar0 uvar2)
  unifyPTys uvar0 uvar1

  pty1 <- zonkDepthPTy 3 uvar0
  pty2 <- zonkDepthPTy 3 uvar1
  pure (pty1, pty2)


public export
test5 : IO ()
test5 = printLn ( runUnifyTyWithoutGeneralizing example5
               == ( Left
                  $ OccursCheckFailed
                      (MkNode 0)
                      (ImpF (UVarTy (MkNode 0)) (UVarTy (MkNode 2)))
                  )
                )

----------------------------------------

public export
interface Monad m => MonadUnifyTy m where
  liftUnifyTy : UnifyTy a -> m a

public export
implementation Monad m => MonadUnifyTy (UnifyTyT m) where
  liftUnifyTy body = MkUnifyTyT $ go body
    where
      go : UnifyTy a -> Impl m a
      go body = do
        let body' : UnionFindT CTy m (Either UnifyTyError a)
            body' = liftUnionFind $ runExceptT $ unUnifyTyT body
        lift body' >>= \case
          Left e => do
            throwE e
          Right a => do
            pure a

public export
implementation MonadUnifyTy m => MonadUnifyTy (ReaderT r m) where
  liftUnifyTy = lift . liftUnifyTy

public export
implementation MonadUnifyTy m => MonadUnifyTy (StateT s m) where
  liftUnifyTy = lift . liftUnifyTy

public export
implementation MonadUnifyTy m => MonadUnifyTy (ExceptT e m) where
  liftUnifyTy = lift . liftUnifyTy

public export
implementation MonadUnifyTy m => MonadUnifyTy (UnionFindT v m) where
  liftUnifyTy = lift . liftUnifyTy
