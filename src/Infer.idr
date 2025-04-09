module Infer

import Control.Monad.State
import Data.SortedMap as Map

import ExceptT
import Ty
import PTy
import Unification
import UnionFind
import UTerm

public export
data InferError
  = VariableUsedTwice String
  | VariableNotConsumed String
  | VariableNotProduced String
  | UnificationError UnificationError

public export
Infer : Type -> Type
Infer = ExceptT InferError Unification

public export
PContext : Type
PContext = SortedMap String PTy

mergeDisjointContexts : PContext -> PContext -> Infer PContext
mergeDisjointContexts ctx1 ctx2 = do
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
   : (String -> InferError)
  -> PContext
  -> PContext
  -> Infer PContext
unifyIdenticalContexts variableNotPresent ctx1 ctx2 = do
  let throws1, throws2, actions : SortedMap String (PTy, String -> Infer PTy)
      throws1 = map (\pty => (pty, throwE . variableNotPresent)) ctx1
      throws2 = map (\pty => (pty, throwE . variableNotPresent)) ctx2
      actions = Map.mergeWith
        (\(pty1, _), (pty2, _) =>
          ( pty1  -- unused
          , \_ => do
              lift $ unify pty1 pty2
              pure pty1
          )
        )
        throws1
        throws2
  let pairs : List (String, Infer PTy)
      pairs = (\(x, (_, action)) => (x, action x))
          <$> Map.toList actions
  
  -- pairs' : List (String, PTy)
  pairs' <- for pairs $ \(x, action) => do
    pty <- action
    pure (x, pty)
  pure $ Map.fromList pairs'

unifyIdenticalGammas : PContext -> PContext -> Infer PContext
unifyIdenticalGammas
  = unifyIdenticalContexts VariableNotConsumed

unifyIdenticalDeltas : PContext -> PContext -> Infer PContext
unifyIdenticalDeltas
  = unifyIdenticalContexts VariableNotProduced

pullVariableFromContext
   : (String -> InferError)
  -> String
  -> PContext
  -> Infer (PTy, PContext)
pullVariableFromContext variableNotPresent x ctx = do
  case Map.lookup x ctx of
    Nothing => do
      throwE $ variableNotPresent x
    Just a => do
      pure (a, Map.delete x ctx)

pullVarFromGamma : String -> PContext -> Infer (PTy, PContext)
pullVarFromGamma
  = pullVariableFromContext VariableNotConsumed

pullVarFromDelta : String -> PContext -> Infer (PTy, PContext)
pullVarFromDelta
  = pullVariableFromContext VariableNotProduced

mutual
  public export
  inferCmd : UCmd -> Infer (PContext, PContext)
  inferCmd (UCut producerA consumerA) = do
    (g, a, d) <- inferProducer producerA
    (g', a', d') <- inferConsumer consumerA
    lift $ unify a a'
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', dd')

  public export
  inferProducer : UProducer -> Infer (PContext, PTy, PContext)
  inferProducer (UVar x) = do
    a <- lift $ newMetaVar
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
    b <- lift $ newMetaVar
    pure (g, PSum a b, d)
  inferProducer (URight producerB) = do
    a <- lift $ newMetaVar
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
  
  public export
  inferConsumer : UConsumer -> Infer (PContext, PTy, PContext)
  inferConsumer (UCoVar x) = do
    a <- lift $ newMetaVar
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
    b <- lift $ newMetaVar
    pure (g, PWith a b, d)
  inferConsumer (USnd consumerB) = do
    a <- lift $ newMetaVar
    (g, b, d) <- inferConsumer consumerB
    pure (g, PWith a b, d)
  inferConsumer (UHandlePar consumerA consumerB) = do
    (g, a, d) <- inferConsumer consumerA
    (g', b, d') <- inferConsumer consumerB
    gg' <- mergeDisjointContexts g g'
    dd' <- mergeDisjointContexts d d'
    pure (gg', PPar a b, dd')
  