-- This module implements System L's typing rules. Given a UTerm, it infers the
-- size of the {co,}context and the types of all the {co,}variables within.
module Infer

import Control.Monad.State
import Data.SortedMap as Map

import Ty
import UTerm
import UTerm.GeneralizeTy
import UTerm.PolyTy
import UTerm.PTy
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.ExceptT

----------------------------------------

public export
data InferError
  = VariableUsedTwice String
  | VariableNotConsumed String
  | VariableNotProduced String
  | UnifyTyError UnifyTyError

public export
record InferT (m : Type -> Type) (a : Type) where
  constructor MkInferT
  unInferT : ExceptT InferError (UnifyTyT m) a

public export
Infer : Type -> Type
Infer = InferT Identity

public export
runInferT
   : Monad m
  => InferT m (GeneralizeTy a)
  -> m (Either InferError a)
runInferT (MkInferT body) = do
  result <- runUnifyTyT $ do
    let mainUnifyAction : UnifyTyT m (Either InferError (GeneralizeTy a))
        mainUnifyAction = runExceptT body
    result <- mainUnifyAction
    case (the (Either InferError (GeneralizeTy a)) result) of
      Left inferError => do
        pure $ do
          pure $ Left inferError
      Right finalGeneralizeAction => do
        pure $ do
          a <- finalGeneralizeAction
          pure $ Right a
  case (the (Either UnifyTyError (Either InferError a)) result) of
    Left unifyError => do
      pure $ Left $ UnifyTyError unifyError
    Right (Left inferError) => do
      pure $ Left inferError
    Right (Right a) => do
      pure $ Right a

public export
runInfer
   : Infer (GeneralizeTy a)
  -> Either InferError a
runInfer body
  = runIdentity $ runInferT body

-----------------------------------------

public export
implementation Monad m => Functor (InferT m) where
  map f (MkInferT m) = MkInferT $ map f m

public export
implementation Monad m => Applicative (InferT m) where
  pure x = MkInferT $ pure x
  (MkInferT f) <*> (MkInferT x) = MkInferT $ f <*> x

public export
implementation Monad m => Monad (InferT m) where
  (MkInferT ma) >>= f = MkInferT $ ma >>= \a => unInferT (f a)

public export
implementation MonadTrans InferT where
  lift = MkInferT . lift . lift

-- Note that InferT discharges the MonadUnifyTy constraint, it does _not_
-- delegate to the m. Being able to unify type variables in an important part of
-- InferT's API.
public export
implementation Monad m => MonadUnifyTy (InferT m) where
  liftUnifyTy body = MkInferT (go body)
    where
      go : UnifyTy a -> ExceptT InferError (UnifyTyT m) a
      go body = do
        let body' : UnifyTyT m a
            body' = liftUnifyTy body
        lift body'

-----------------------------------------

mergeDisjointContexts
   : Monad m
  => PContext
  -> PContext
  -> InferT m PContext
mergeDisjointContexts ctx1 ctx2 = MkInferT $ do
  let falses1, falses2, bools : SortedMap String Bool
      falses1 = map (const False) ctx1
      falses2 = map (const False) ctx2
      bools = Map.mergeWith (\x, y => True) falses1 falses2
  let pairs, trues : List (String, Bool)
      pairs = Map.toList bools
      trues = filter snd pairs
  let conflictingVars : List String
      conflictingVars = map fst trues
  case conflictingVars of
    [] => do
      pure $ Map.mergeLeft ctx1 ctx2
    x::_ => do
      throwE $ VariableUsedTwice x

unifyIdenticalContexts
   : Monad m
  => (String -> InferError)
  -> PContext
  -> PContext
  -> InferT m PContext
unifyIdenticalContexts variableNotPresent ctx1 ctx2 = MkInferT $ do
  let throws1, throws2, actions : SortedMap String (PTy, String -> ExceptT InferError (UnifyTyT m) PTy)
      throws1 = map (\pty => (pty, throwE . variableNotPresent)) ctx1
      throws2 = map (\pty => (pty, throwE . variableNotPresent)) ctx2
      actions = Map.mergeWith
        (\(pty1, _), (pty2, _) =>
          ( pty1  -- unused
          , \_ => do
              lift $ unifyPTys pty1 pty2
              pure pty1
          )
        )
        throws1
        throws2
  let pairs : List (String, ExceptT InferError (UnifyTyT m) PTy)
      pairs = (\(x, (_, action)) => (x, action x))
          <$> Map.toList actions

  -- pairs' : List (String, PTy)
  pairs' <- for pairs $ \(x, action) => do
    pty <- action
    pure (x, pty)
  pure $ Map.fromList pairs'

unifyIdenticalGammas
   : Monad m
  => PContext
  -> PContext
  -> InferT m PContext
unifyIdenticalGammas
  = unifyIdenticalContexts VariableNotConsumed

unifyIdenticalDeltas
   : Monad m
  => PContext
  -> PContext
  -> InferT m PContext
unifyIdenticalDeltas
  = unifyIdenticalContexts VariableNotProduced

pullVariableFromContext
   : Monad m
  => (String -> InferError)
  -> String
  -> PContext
  -> InferT m (PTy, PContext)
pullVariableFromContext variableNotPresent x ctx = MkInferT $ do
  case Map.lookup x ctx of
    Nothing => do
      throwE $ variableNotPresent x
    Just a => do
      pure (a, Map.delete x ctx)

pullVarFromGamma
   : Monad m
  => String
  -> PContext
  -> InferT m (PTy, PContext)
pullVarFromGamma
  = pullVariableFromContext VariableNotConsumed

pullVarFromDelta
   : Monad m
  => String
  -> PContext
  -> InferT m (PTy, PContext)
pullVarFromDelta
  = pullVariableFromContext VariableNotProduced

mutual
  inferCmd
     : Monad m
    => UCmd
    -> InferT m (PContext, PContext)
  inferCmd (UCut producerA consumerA) = do
    (g, a, d) <- inferProducer producerA
    (g', a', d') <- inferConsumer consumerA
    liftUnifyTy $ unifyPTys a a'
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', dd')

  inferProducer
     : Monad m
    => UProducer
    -> InferT m (PContext, PTy, PContext)
  inferProducer (UVar x) = do
    a <- liftUnifyTy $ newUVarTy
    pure (Map.singleton x a, a, Map.empty)
  inferProducer (UMu x g_to_ad) = do
    (g, ad) <- inferCmd g_to_ad
    (a, d) <- pullVarFromDelta x ad
    pure (g, a, d)
  inferProducer (ULam x y ag_to_bd) = do
    (ag, bd) <- inferCmd ag_to_bd
    (a, g) <- pullVarFromGamma x ag
    (b, d) <- pullVarFromDelta y bd
    pure (g, PImp a b, d)
  inferProducer (UConnect consumerA producerB) = do
    (g, a, d) <- inferConsumer consumerA
    (g', b, d') <- inferProducer producerB
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', PBridge a b, dd')
  inferProducer (UPair producerA producerB) = do
    (g, a, d) <- inferProducer producerA
    (g', b, d') <- inferProducer producerB
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', PTen a b, dd')
  inferProducer (ULeft producerA) = do
    (g, a, d) <- inferProducer producerA
    b <- liftUnifyTy $ newUVarTy
    pure (g, PSum a b, d)
  inferProducer (URight producerB) = do
    a <- liftUnifyTy $ newUVarTy
    (g, b, d) <- inferProducer producerB
    pure (g, PSum a b, d)
  inferProducer (UCoMatchWith producerA producerB) = do
    (g, a, d) <- inferProducer producerA
    (g', b, d') <- inferProducer producerB
    gg' <- unifyIdenticalGammas g g'
    dd' <- unifyIdenticalDeltas d d'
    pure (gg', PWith a b, dd')
  inferProducer (UCoMatchPar x y g_to_abd) = do
    (g, abd) <- inferCmd g_to_abd
    (a, bd) <- pullVarFromDelta x abd
    (b, d) <- pullVarFromDelta y bd
    pure (g, PPar a b, d)

  inferConsumer
     : Monad m
    => UConsumer
    -> InferT m (PContext, PTy, PContext)
  inferConsumer (UCoVar x) = do
    a <- liftUnifyTy $ newUVarTy
    pure (Map.empty, a, Map.singleton x a)
  inferConsumer (UCoMu x cmd) = do
    (g, d) <- inferCmd cmd
    (a, g') <- pullVarFromGamma x g
    pure (g', a, d)
  inferConsumer (UApp producerA consumerB) = do
    (g, a, d) <- inferProducer producerA
    (g', b, d') <- inferConsumer consumerB
    gg' <- unifyIdenticalGammas g g'
    dd' <- unifyIdenticalDeltas d d'
    pure (gg', PImp a b, dd')
  inferConsumer (UMatchBridge x y bg_to_ad) = do
    (bg, ad) <- inferCmd bg_to_ad
    (b, g) <- pullVarFromGamma y bg
    (a, d) <- pullVarFromDelta x ad
    pure (g, PBridge a b, d)
  inferConsumer (UMatchPair x y abg_to_d) = do
    (abg, d) <- inferCmd abg_to_d
    (a, bg) <- pullVarFromGamma x abg
    (b, g) <- pullVarFromGamma y bg
    pure (g, PTen a b, d)
  inferConsumer (UMatchSum consumerA consumerB) = do
    (g, a, d) <- inferConsumer consumerA
    (g', b, d') <- inferConsumer consumerB
    gg' <- unifyIdenticalGammas g g'
    dd' <- unifyIdenticalDeltas d d'
    pure (gg', PSum a b, dd')
  inferConsumer (UFst consumerA) = do
    (g, a, d) <- inferConsumer consumerA
    b <- liftUnifyTy $ newUVarTy
    pure (g, PWith a b, d)
  inferConsumer (USnd consumerB) = do
    a <- liftUnifyTy $ newUVarTy
    (g, b, d) <- inferConsumer consumerB
    pure (g, PWith a b, d)
  inferConsumer (UHandlePar consumerA consumerB) = do
    (g, a, d) <- inferConsumer consumerA
    (g', b, d') <- inferConsumer consumerB
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', PPar a b, dd')

public export
runInferCmd
   : UCmd
  -> Either InferError (PolyContext, PolyContext)
runInferCmd cmd = runInfer $ do
  (g, d) <- inferCmd cmd
  pure $ generalizePair g d

public export
runInferProducer
   : UProducer
  -> Either InferError (PolyContext, PolyTy, PolyContext)
runInferProducer producer = runInfer $ do
  (g, a, d) <- inferProducer producer
  pure $ generalizeTriple g a d

public export
runInferConsumer
   : UConsumer
  -> Either InferError (PolyContext, PolyTy, PolyContext)
runInferConsumer consumer = runInfer $ do
  (g, a, d) <- inferConsumer consumer
  pure $ generalizeTriple g a d

----------------------------------------

public export
implementation Show InferError where
  showPrec p (VariableUsedTwice x)
    = showParens (p /= Open)
    $ "VariableUsedTwice " ++ showPrec App x
  showPrec p (VariableNotConsumed x)
    = showParens (p /= Open)
    $ "VariableNotConsumed " ++ showPrec App x
  showPrec p (VariableNotProduced x)
    = showParens (p /= Open)
    $ "VariableNotProduced " ++ showPrec App x
  showPrec p (UnifyTyError e)
    = showPrec p e

public export
implementation Eq InferError where
  VariableUsedTwice x1 == VariableUsedTwice x2
    = x1 == x2
  VariableNotConsumed x1 == VariableNotConsumed x2
    = x1 == x2
  VariableNotProduced x1 == VariableNotProduced x2
    = x1 == x2
  UnifyTyError e1 == UnifyTyError e2
    = e1 == e2
  _ == _
    = False

-----------------------------------------

public export
interface Monad m => MonadInfer m where
  liftInfer : Infer a -> m a

public export
implementation Monad m => MonadInfer (InferT m) where
  liftInfer body = MkInferT $ go body
    where
      go : Infer a -> ExceptT InferError (UnifyTyT m) a
      go body = do
        let body' : UnifyTyT m (Either InferError a)
            body' = liftUnifyTy $ runExceptT $ unInferT body
        lift body' >>= \case
          Left e => do
            throwE e
          Right a => do
            pure a

public export
implementation MonadInfer m => MonadInfer (StateT s m) where
  liftInfer body = lift $ liftInfer body

public export
implementation MonadInfer m => MonadInfer (ExceptT e m) where
  liftInfer body = lift $ liftInfer body
