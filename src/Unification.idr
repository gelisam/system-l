module Unification

import Control.Monad.State
import Data.Maybe
import Data.SortedMap as Map

import ExceptT
import PolyTy
import PTy
import Ty
import UnionFind

public export
data UnificationError
  = OccursCheckFailed Root CTy
  | TypeMismatch CTy CTy

public export
Unification : Type -> Type
Unification = ExceptT UnificationError (UnionFind CTy)

public export
runUnification : Unification a -> Either UnificationError a
runUnification body = do
  runUF (runExceptT body)

public export
newMetaVar : Unification PTy
newMetaVar = do
  node <- lift $ newNode Nothing
  pure $ MetaVar node

public export
occursCheck : Node -> CTy -> Unification ()
occursCheck needleNode cty = do
  root <- lift $ findRoot needleNode
  bools <- traverse (rootOccursInPTy root) cty
  if any id bools
    then throwE $ OccursCheckFailed root cty
    else pure ()
  where
    rootOccursInPTy : Root -> PTy -> Unification Bool
    rootOccursInPTy needleRoot pty = do
      let go : PTy -> Unification Bool
          go (MetaVar node) = do
            root <- lift $ findRoot node
            pure (root == needleRoot)
          go (Ctor cty) = do
            bools <- traverse go cty
            pure $ any id bools
      go pty

public export
zonk : PTy -> Unification PTy
zonk (MetaVar node) = do
  root <- lift $ findRoot node
  (lift $ getValue root) >>= \case
    Nothing => 
      pure $ MetaVar root
    Just cty => do
      cty' <- traverse zonk cty
      pure $ Ctor cty'
zonk (Ctor cty) = do
  cty' <- traverse zonk cty
  pure $ Ctor cty'

mutual
  unifyMetaVars : Node -> Node -> Unification ()
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
  
  unifyMetaVarWithCty : Node -> CTy -> Unification ()
  unifyMetaVarWithCty node1 cty2 = do
    root1 <- lift $ findRoot node1
    (lift $ getValue root1) >>= \case
      Nothing => do
        occursCheck root1 cty2
        lift $ setValue root1 $ Just cty2
      Just cty1 => 
        unifyCTys cty1 cty2
  
  unifyPTys : PTy -> PTy -> Unification ()
  unifyPTys (MetaVar node1) (MetaVar node2) = 
    unifyMetaVars node1 node2
  unifyPTys (MetaVar node) (Ctor cty) = 
    unifyMetaVarWithCty node cty
  unifyPTys (Ctor cty) (MetaVar node) = 
    unifyMetaVarWithCty node cty
  unifyPTys (Ctor cty1) (Ctor cty2) = 
    unifyCTys cty1 cty2
  
  unifyCTys : CTy -> CTy -> Unification ()
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
  unifyCTys cty1 cty2 = 
    throwE (TypeMismatch cty1 cty2)

public export
unify : PTy -> PTy -> Unification ()
unify = unifyPTys

-- Replace _all_ the unification variables to quantified variables. Note that
-- this is only reasonable for top-level types, this implementation would not
-- work for let-generalization.
public export
generalize : PTy -> Unification PolyTy
generalize pty = do
  zonked <- zonk pty
  evalStateT Map.empty (go zonked)
  where
    go : PTy -> StateT (SortedMap Node Nat) Unification PolyTy
    go (MetaVar node) = do
      nodeToQVar <- get
      case lookup node nodeToQVar of
        Nothing => do
          let newQVar = length (Map.toList nodeToQVar)
          let nodeToQVar' = insert node newQVar nodeToQVar
          put nodeToQVar'
          pure $ QVar newQVar
        Just qvar => do
          pure $ QVar qvar
    go (Ctor cty) = do
      cty' <- traverse go cty
      pure $ Ctor cty'

public export
showUnificationError : UnificationError -> String
showUnificationError (OccursCheckFailed node pty) = 
  "Occurs check failed: Node " ++ showPrec App node ++ " occurs in " ++ showPrec App pty
showUnificationError (TypeMismatch cty1 cty2) = 
  "Type mismatch: Cannot unify " ++ showPrec App cty1 ++ " with " ++ showPrec App cty2

public export
implementation Show UnificationError where
  showPrec p (OccursCheckFailed node pty)
    = showParens (p /= Open)
    $ "OccursCheckFailed " ++ showPrec App node ++ " " ++ showPrec App pty
  showPrec p (TypeMismatch cty1 cty2)
    = showParens (p /= Open)
    $ "TypeMismatch " ++ showPrec App cty1 ++ " " ++ showPrec App cty2

public export
implementation Eq UnificationError where
  OccursCheckFailed node1 pty1 == OccursCheckFailed node2 pty2
    = node1 == node2
   && pty1 == pty2
  TypeMismatch cty1 cty2 == TypeMismatch cty3 cty4
    = cty1 == cty3
   && cty2 == cty4
  _ == _
    = False


example1 : Unification PolyTy
example1 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  meta3 <- newMetaVar
  meta4 <- newMetaVar
  unify (PImp meta1 meta2) (PImp meta2 meta3)
  generalize $ PImp meta1 $ PImp meta2 $ PImp meta3 meta4

public export
test1 : IO ()
test1 = printLn ( runUnification example1
               == ( Right
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0)
                  $ PolyImp (QVar 0) (QVar 1)
                  )
                )

example2 : Unification ()
example2 = do
  meta1 <- newMetaVar
  meta2 <- newMetaVar
  meta3 <- newMetaVar
  unify (PImp meta1 meta2) (PPar meta2 meta3)

public export
test2 : IO ()
test2 = printLn ( runUnification example2
               == ( Left
                  $ TypeMismatch
                      (ImpF (MetaVar 0) (MetaVar 1))
                      (ParF (MetaVar 1) (MetaVar 2))
                  )
                )