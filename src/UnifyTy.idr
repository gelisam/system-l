module UnifyTy

import Control.Monad.State
import Data.Maybe
import Data.SortedMap as Map

import ExceptT
import PolyTy
import PTy
import Ty
import UnionFind

----------------------------------------

public export
PContext : Type
PContext = SortedMap String PTy

public export
PolyContext : Type
PolyContext = List (String, PolyTy)

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

public export
runUnifyTyT : Monad m => UnifyTyT m a -> m (Either UnifyTyError a)
runUnifyTyT (MkUnifyTyT body) = runUnionFindT (runExceptT body)

public export
runUnifyTy : UnifyTy a -> Either UnifyTyError a
runUnifyTy = runIdentity . runUnifyTyT

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
  (MkUnifyTyT ma) >>= f = MkUnifyTyT $ ma >>= \a => unUnifyTyT (f a)

-----------------------------------------

public export
newMetaVar : Monad m => UnifyTyT m PTy
newMetaVar = MkUnifyTyT $ do
  node <- lift $ newNode Nothing
  pure $ MetaVar node

public export
occursCheck
   : Monad m
  => Node
  -> CTy
  -> ExceptT UnifyTyError (UnionFindT CTy m) ()
occursCheck needleNode cty = do
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
          go (MetaVar node) = do
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
zonkImpl (MetaVar node) = do
  root <- lift $ findRoot node
  (lift $ getValue root) >>= \case
    Nothing => 
      pure $ MetaVar root
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
  unifyMetaVars
     : Monad m
    => Node
    -> Node
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyMetaVars node1 node2 = do
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
            unifyCTys cty1 cty2 
            lift $ union root1 root2 (Just cty1)
  
  unifyMetaVarWithCty
     : Monad m
    => Node
    -> CTy
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyMetaVarWithCty node1 cty2 = do
    root1 <- lift $ findRoot node1
    (lift $ getValue root1) >>= \case
      Nothing => do
        occursCheck root1 cty2
        lift $ setValue root1 $ Just cty2
      Just cty1 => 
        unifyCTys cty1 cty2
  
  unifyPTys
     : Monad m
    => PTy
    -> PTy
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyPTys (MetaVar node1) (MetaVar node2) = 
    unifyMetaVars node1 node2
  unifyPTys (MetaVar node) (Ctor cty) = 
    unifyMetaVarWithCty node cty
  unifyPTys (Ctor cty) (MetaVar node) = 
    unifyMetaVarWithCty node cty
  unifyPTys (Ctor cty1) (Ctor cty2) = 
    unifyCTys cty1 cty2
  
  unifyCTys
     : Monad m
    => CTy
    -> CTy
    -> ExceptT UnifyTyError (UnionFindT CTy m) ()
  unifyCTys (ImpF a1 b1) (ImpF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys (BridgeF a1 b1) (BridgeF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys (TenF a1 b1) (TenF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys (SumF a1 b1) (SumF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys (WithF a1 b1) (WithF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys (ParF a1 b1) (ParF a2 b2) = do
    unifyPTys a1 a2
    unifyPTys b1 b2
  unifyCTys cty1 cty2 = do
    throwE (TypeMismatch cty1 cty2)

public export
unify : Monad m => PTy -> PTy -> UnifyTyT m ()
unify pty1 pty2 = MkUnifyTyT $ do
  unifyPTys pty1 pty2

generalizeZonked
   : Monad m
  => PTy
  -> StateT (SortedMap Node Nat) (UnifyTyT m) PolyTy
generalizeZonked (MetaVar node) = do
  nodeToQVar <- get
  case lookup node nodeToQVar of
    Nothing => do
      let newQVar = length (Map.toList nodeToQVar)
      let nodeToQVar' = insert node newQVar nodeToQVar
      put nodeToQVar'
      pure $ QVar newQVar
    Just qvar => do
      pure $ QVar qvar
generalizeZonked (Ctor cty) = do
  cty' <- traverse generalizeZonked cty
  pure $ Ctor cty'

generalizeContext
   : Monad m
  => PContext
  -> StateT (SortedMap Node Nat) (UnifyTyT m) PolyContext
generalizeContext ctx = do
  for (Map.toList ctx) $ \(x, pty) => do
    zonked <- lift $ zonk pty
    poly <- generalizeZonked zonked
    pure (x, poly)

-- Replace _all_ the unification variables to quantified variables. Note that
-- this is only reasonable for top-level types, this implementation would not
-- work for let-generalization.
public export
generalize : Monad m => PTy -> UnifyTyT m PolyTy
generalize pty = evalStateT Map.empty $ do
  zonked <- lift $ zonk pty
  generalizeZonked zonked

public export
generalizePair
   : Monad m
  => PContext
  -> PContext
  -> UnifyTyT m (PolyContext, PolyContext)
generalizePair g d = evalStateT Map.empty $ do
  g' <- generalizeContext g
  d' <- generalizeContext d
  pure (g', d')

public export
generalizeTriple
   : Monad m
  => PContext
  -> PTy
  -> PContext
  -> UnifyTyT m (PolyContext, PolyTy, PolyContext)
generalizeTriple g pty d = evalStateT Map.empty $ do
  g' <- generalizeContext g
  zonked <- lift $ zonk pty
  poly <- generalizeZonked zonked
  d' <- generalizeContext d
  pure (g', poly, d')

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

example1 : UnifyTy PolyTy
example1 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  meta3 <- newMetaVar
  meta4 <- newMetaVar
  unify (PImp meta1 meta2) (PImp meta2 meta3)
  generalize $ PImp meta1 $ PImp meta2 $ PImp meta3 meta4

public export
test1 : IO ()
test1 = printLn ( runUnifyTy example1
               == ( Right
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0) (QVar 1)
                  )
                )

example2 : UnifyTy ()
example2 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  meta3 <- newMetaVar
  unify (PImp meta1 meta2) (PPar meta2 meta3)

public export
test2 : IO ()
test2 = printLn ( runUnifyTy example2
               == ( Left
                  $ TypeMismatch
                      (ImpF (MetaVar 0) (MetaVar 1))
                      (ParF (MetaVar 1) (MetaVar 2))
                  )
                )

example3 : UnifyTy ()
example3 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  unify meta1 (PImp meta1 meta2)

public export
test3 : IO ()
test3 = printLn ( runUnifyTy example3
               == ( Left
                  $ OccursCheckFailed
                      0
                      (ImpF (MetaVar 0) (MetaVar 1))
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
