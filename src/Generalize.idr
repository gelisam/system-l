-- Once all the type equations from the typing rules have been applied and we
-- have learned all there is to learn about the shape of the types involved, if
-- there are portions in a PTy for which we still haven't pinned down which type
-- they should be, that means that any type would have worked. In that case, we
-- "generalize" the PTy into a PolyTy, to indicate which parts can be any type.
module Generalize

import Control.Monad.State
import Data.SortedMap as Map

import PolyTy
import PTy
import Ty
import UnifyTy
import UnionFind

----------------------------------------

public export
PContext : Type
PContext = SortedMap String PTy

public export
PolyContext : Type
PolyContext = List (String, PolyTy)

public export
record Generalize a where
  constructor MkGeneralize
  unGeneralize : StateT (SortedMap Node Nat) UnifyTy a

-- This language does not have let-generalization, so we can simply replace all
-- the unification variables with quantified variables. This API encourages
-- correct usage, namely generalizing everything at the very end of a UnifyTy
-- computation so that the unification variables cannot be used again.
public export
runUnifyTyT
   : Monad m
  => UnifyTyT m a
  -> (a -> Generalize b)
  -> m (Either UnifyTyError b)
runUnifyTyT body1 generalizeA = do
  runUnifyTyTWithoutGeneralizing $ do
    x <- body1
    let body2' : Generalize b
        body2' = generalizeA x
        body2'' : UnifyTy b
        body2'' = evalStateT Map.empty $ unGeneralize body2'
    liftUnifyTy body2''

public export
runUnifyTy
   : UnifyTy a
  -> (a -> Generalize b)
  -> Either UnifyTyError b
runUnifyTy body1 generalizeA
  = runIdentity $ runUnifyTyT body1 generalizeA

----------------------------------------

public export
implementation Functor Generalize where
  map f (MkGeneralize m)
    = MkGeneralize $ map f m

public export
implementation Applicative Generalize where
  pure x
    = MkGeneralize $ pure x
  (MkGeneralize f) <*> (MkGeneralize x)
    = MkGeneralize $ f <*> x

public export
implementation Monad Generalize where
  (MkGeneralize ma) >>= f
    = MkGeneralize $ ma >>= \a => unGeneralize (f a)

----------------------------------------

generalizeZonkedImpl
   : PTy
  -> StateT (SortedMap Node Nat) UnifyTy PolyTy
generalizeZonkedImpl (MetaVar node) = do
  nodeToQVar <- get
  case lookup node nodeToQVar of
    Nothing => do
      let newQVar = length (Map.toList nodeToQVar)
      let nodeToQVar' = insert node newQVar nodeToQVar
      put nodeToQVar'
      pure $ QVar newQVar
    Just qvar => do
      pure $ QVar qvar
generalizeZonkedImpl (Ctor cty) = do
  cty' <- traverse generalizeZonkedImpl cty
  pure $ Ctor cty'

public export
generalizeType : PTy -> Generalize PolyTy
generalizeType pty = MkGeneralize $ do
  zonked <- lift $ zonk pty
  generalizeZonkedImpl zonked

public export
generalizeContext : PContext -> Generalize PolyContext
generalizeContext ctx = do
  for (Map.toList ctx) $ \(x, pty) => do
    poly <- generalizeType pty
    pure (x, poly)

public export
generalizePair : PContext -> PContext -> Generalize (PolyContext, PolyContext)
generalizePair g d = do
  g' <- generalizeContext g
  d' <- generalizeContext d
  pure (g', d')

public export
generalizeTriple : PContext -> PTy -> PContext -> Generalize (PolyContext, PolyTy, PolyContext)
generalizeTriple g pty d = do
  g' <- generalizeContext g
  poly <- generalizeType pty
  d' <- generalizeContext d
  pure (g', poly, d')

----------------------------------------

example1 : UnifyTy PTy
example1 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  meta3 <- newMetaVar
  meta4 <- newMetaVar
  unify (PImp meta1 meta2) (PImp meta2 meta3)
  pure $ PImp meta1 $ PImp meta2 $ PImp meta3 meta4

public export
test1 : IO ()
test1 = printLn ( runUnifyTy example1 generalizeType
               == ( Right
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0) (QVar 1)
                  )
                )
