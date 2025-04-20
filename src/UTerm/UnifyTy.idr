-- "UnifyTy" stands for "Unification for Types". This module can unify two
-- PTy's, figuring out which Ty the unification variables at matching positions
-- must refer to and detecting contradictions. The module "Infer.idr" uses this
-- when traversing a UTerm to make sure that two types which are supposed to be
-- equal according to the typing rules really are equal.
module UTerm.UnifyTy

import Control.Monad.State

import Ty
import UTerm.ExceptT
import UTerm.PTy
import UTerm.UnionFind

----------------------------------------

public export
data UnifyTyError
  = OccursCheckFailed Root CTy
  | TypeMismatch CTy CTy

public export
record UnifyTyT (m : Type -> Type) (a : Type) where
  constructor MkUnifyTyT
  unUnifyTyT : ExceptT UnifyTyError (UnionFindT CTy m) a

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
  map f (MkUnifyTyT m) = MkUnifyTyT $ map f m

public export
implementation Monad m => Applicative (UnifyTyT m) where
  pure x = MkUnifyTyT $ pure x
  (MkUnifyTyT f) <*> (MkUnifyTyT x) = MkUnifyTyT $ f <*> x

public export
implementation Monad m => Monad (UnifyTyT m) where
  (MkUnifyTyT ma) >>= f
    = MkUnifyTyT (ma >>= \a => unUnifyTyT (f a))

-----------------------------------------

public export
newUVarTy : Monad m => UnifyTyT m PTy
newUVarTy = MkUnifyTyT $ do
  node <- lift $ newNode Nothing
  pure $ UVarTy node

occursCheckImpl
   : Monad m
  => Node
  -> CTy
  -> ExceptT UnifyTyError (UnionFindT CTy m) ()
occursCheckImpl needleNode cty = do
  root <- lift $ findRoot needleNode
  bools <- traverse (rootOccursInPTy root) cty
  if any id bools
    then throwE $ OccursCheckFailed root cty
    else pure ()
  where
    rootOccursInPTy
       : Root
      -> PTy
      -> ExceptT UnifyTyError (UnionFindT CTy m) Bool
    rootOccursInPTy needleRoot pty = do
      let go : PTy -> ExceptT UnifyTyError (UnionFindT CTy m) Bool
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
  => PTy
  -> ExceptT UnifyTyError (UnionFindT CTy m) PTy
zonkImpl (UVarTy node) = do
  root <- lift $ findRoot node
  (lift $ getValue root) >>= \case
    Nothing => 
      pure $ UVarTy root
    Just cty => do
      cty' <- traverse zonkImpl cty
      pure $ Ctor cty'
zonkImpl (Ctor cty) = do
  cty' <- traverse zonkImpl cty
  pure $ Ctor cty'

public export
zonk : Monad m => PTy -> UnifyTyT m PTy
zonk pty = MkUnifyTyT $ do
  zonkImpl pty

mutual
  unifyUVarTysImpl
     : Monad m
    => Node
    -> Node
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyUVarTysImpl node1 node2 = do
    root1 <- lift $ findRoot node1
    root2 <- lift $ findRoot node2
    if root1 == root2
      then pure ()
      else do
        maybeV1 <- lift $ getValue root1
        maybeV2 <- lift $ getValue root2
        case (maybeV1, maybeV2) of
          (Nothing, Nothing) => 
            lift $ union root1 root2 Nothing
          (Just cty1, Nothing) => 
            lift $ union root1 root2 (Just cty1)
          (Nothing, Just cty2) => 
            lift $ union root1 root2 (Just cty2)
          (Just cty1, Just cty2) => do
            unifyCTysImpl cty1 cty2 
            lift $ union root1 root2 (Just cty1)
  
  unifyUVarTyWithCtyImpl
     : Monad m
    => Node
    -> CTy
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
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
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
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
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyCTysImpl (ImpF a1 b1) (ImpF a2 b2) = do
    unifyPTysImpl a1 a2
    unifyPTysImpl b1 b2
  unifyCTysImpl (BridgeF a1 b1) (BridgeF a2 b2) = do
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
showUnifyTyError (OccursCheckFailed node pty) = 
  "Occurs check failed: Node " ++ showPrec App node ++ " occurs in " ++ showPrec App pty
showUnifyTyError (TypeMismatch cty1 cty2) = 
  "Type mismatch: Cannot unify " ++ showPrec App cty1 ++ " with " ++ showPrec App cty2

----------------------------------------

public export
implementation Show UnifyTyError where
  showPrec p (OccursCheckFailed node pty)
    = showParens (p /= Open)
    $ "OccursCheckFailed " ++ showPrec App node ++ " " ++ showPrec App pty
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
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy
  uvar3 <- newUVarTy
  uvar4 <- newUVarTy
  unifyPTys (PImp uvar1 uvar2) (PImp uvar2 uvar3)
  zonk $ PImp uvar1 $ PImp uvar2 $ PImp uvar3 uvar4

-- The algorithm doesn't guarantee which variable is chosen as the root, so what I really want to test is that there are two distinct nodes n1 and n2 such that the result is
--
--   Right $ PImp n1 $ PImp n1 $ PImp n1 n2
--
-- But it is much easier to just inspect the result and use the roots 0 and 3 which happen to be chosen by the algorithm and use that as the test case.
public export
test1 : IO ()
test1 = printLn ( runUnifyTyWithoutGeneralizing example1
               == ( Right
                  $ PImp (UVarTy 0)
                  $ PImp (UVarTy 0)
                  $ PImp (UVarTy 0) (UVarTy 3)
                  )
                )

example2 : UnifyTy ()
example2 = do
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy
  uvar3 <- newUVarTy
  unifyPTys (PImp uvar1 uvar2) (PPar uvar2 uvar3)

public export
test2 : IO ()
test2 = printLn ( runUnifyTyWithoutGeneralizing example2
               == ( Left
                  $ TypeMismatch
                      (ImpF (UVarTy 0) (UVarTy 1))
                      (ParF (UVarTy 1) (UVarTy 2))
                  )
                )

example3 : UnifyTy ()
example3 = do
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy
  unifyPTys uvar1 (PImp uvar1 uvar2)

public export
test3 : IO ()
test3 = printLn ( runUnifyTyWithoutGeneralizing example3
               == ( Left
                  $ OccursCheckFailed
                      0
                      (ImpF (UVarTy 0) (UVarTy 1))
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
      go : UnifyTy a -> ExceptT UnifyTyError (UnionFindT CTy m) a
      go body = do
        let body' : UnionFindT CTy m (Either UnifyTyError a)
            body' = liftUnionFind $ runExceptT $ unUnifyTyT body
        lift body' >>= \case
          Left e => do
            throwE e
          Right a => do
            pure a

public export
implementation MonadUnifyTy m => MonadUnifyTy (StateT s m) where
  liftUnifyTy body = lift $ liftUnifyTy body

public export
implementation MonadUnifyTy m => MonadUnifyTy (ExceptT e m) where
  liftUnifyTy body = lift $ liftUnifyTy body
