-- Once all the type equations from the typing rules have been applied and we
-- have learned all there is to learn about the shape of the types involved, if
-- there are portions in a PTy for which we still haven't pinned down which type
-- they should be, that means that any type would have worked. In that case, we
-- "generalize" the PTy into a PolyTy, to indicate which parts can be any type.
module UTerm.GeneralizeTy

import Control.Monad.State
import Data.SortedMap as Map

import Ty
import UTerm.PolyTy
import UTerm.PTy
import UTerm.UnifyTy
import UTerm.UnionFind

----------------------------------------

public export
PContext : Type
PContext = SortedMap String PTy

public export
PolyContext : Type
PolyContext = List (String, PolyTy)

public export
record GeneralizeTy a where
  constructor MkGeneralizeTy
  unGeneralizeTy : StateT (SortedMap Node Nat) UnifyTy a

-- This language does not have let-generalization, so we can simply replace all
-- the unification variables with quantified variables.
--
-- Note that the input not a monad stack which allows both UnifyTy and
-- GeneralizeTy effects to be interleaved, it is a UnifyTy computation followed
-- by a GeneralizeTy computation. This API encourages correct usage, namely
-- generalizing everything at the very end so that the unification variables
-- cannot be used again.
public export
runUnifyTyT
   : Monad m
  => UnifyTyT m (GeneralizeTy a)
  -> m (Either UnifyTyError a)
runUnifyTyT mainUnifyAction = do
  runUnifyTyTWithoutGeneralizing $ do
    finalGeneralizeAction <- mainUnifyAction
    let finalUnifyAction : UnifyTy a
        finalUnifyAction = evalStateT Map.empty $ unGeneralizeTy finalGeneralizeAction
    liftUnifyTy finalUnifyAction

public export
runUnifyTy
   : UnifyTy (GeneralizeTy a)
  -> Either UnifyTyError a
runUnifyTy body
  = runIdentity $ runUnifyTyT body

----------------------------------------

public export
implementation Functor GeneralizeTy where
  map f (MkGeneralizeTy body)
    = MkGeneralizeTy $ map f body

public export
implementation Applicative GeneralizeTy where
  pure x
    = MkGeneralizeTy $ pure x
  (MkGeneralizeTy f) <*> (MkGeneralizeTy x)
    = MkGeneralizeTy $ f <*> x

public export
implementation Monad GeneralizeTy where
  (MkGeneralizeTy ma) >>= f
    = MkGeneralizeTy $ ma >>= \a => unGeneralizeTy (f a)

----------------------------------------

generalizeZonkedImpl
   : PTy
  -> StateT (SortedMap Node Nat) UnifyTy PolyTy
generalizeZonkedImpl (UVarTy node) = do
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
generalizeType : PTy -> GeneralizeTy PolyTy
generalizeType pty = MkGeneralizeTy $ do
  zonked <- lift $ zonk pty
  generalizeZonkedImpl zonked

public export
generalizeContext : PContext -> GeneralizeTy PolyContext
generalizeContext ctx = do
  for (Map.toList ctx) $ \(x, pty) => do
    poly <- generalizeType pty
    pure (x, poly)

public export
generalizePair : PContext -> PContext -> GeneralizeTy (PolyContext, PolyContext)
generalizePair g d = do
  g' <- generalizeContext g
  d' <- generalizeContext d
  pure (g', d')

public export
generalizeTriple : PContext -> PTy -> PContext -> GeneralizeTy (PolyContext, PolyTy, PolyContext)
generalizeTriple g pty d = do
  g' <- generalizeContext g
  poly <- generalizeType pty
  d' <- generalizeContext d
  pure (g', poly, d')

----------------------------------------

example1 : UnifyTy (GeneralizeTy PolyTy)
example1 = do
  uvar1 <- newUVarTy
  uvar2 <- newUVarTy
  uvar3 <- newUVarTy
  uvar4 <- newUVarTy
  unifyPTys (PImp uvar1 uvar2) (PImp uvar2 uvar3)
  pure $ do
    generalizeType $ PImp uvar1 $ PImp uvar2 $ PImp uvar3 uvar4

public export
test1 : IO ()
test1 = printLn ( runUnifyTy example1
               == ( Right
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0) (QVar 1)
                  )
                )
