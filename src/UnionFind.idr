module UnionFind

import Control.Monad.State
import Data.Maybe
import Data.SortedMap

import ExceptT

----------------------------------------

-- A `Node` points to a value of type `Maybe v`. If it has been unioned with
-- other Nodes, all the nodes in the set points to the same `Maybe v`.
public export
Node : Type
Node = Nat

-- A representative of the set. Which Node is the Root may change after a union
-- operation.
public export
Root : Type
Root = Node

-- The internal state of the UnionFind monad.
record S v where
  constructor MkS
  -- For 'newNode'.
  nextNode : Node
  -- Following the chain of parents always leads to a Root, which does not have
  -- a parent.
  parents : SortedMap Node Node
  -- Missing keys map to 'Nothing'.
  values : SortedMap Root v
  -- The approximate worst-case number of parent-to-parent hops needed for a
  -- Node to reach this Root. Missing keys map to 0.
  ranks : SortedMap Root Nat

-- Wrapped in a State monad for easier manipulation.
public export
record UnionFindT (v : Type) (m : Type -> Type) (a : Type) where
  constructor MkUnionFindT
  unUnionFindT : StateT (S v) m a

public export
UnionFind : Type -> Type -> Type
UnionFind v = UnionFindT v Identity

public export
runUnionFindT : Monad m => UnionFindT v m a -> m a
runUnionFindT (MkUnionFindT body) = evalStateT (MkS 0 empty empty empty) body

public export
runUnionFind : UnionFind v a -> a
runUnionFind = runIdentity . runUnionFindT

public export
newNode : Monad m => Maybe v -> UnionFindT v m Node
newNode maybeV = MkUnionFindT $ do
  MkS newNode parents values ranks <- get
  let values' = case maybeV of
                  Just v
                    => insert newNode v values
                  Nothing
                    => values
  put $ MkS (newNode + 1) parents values' ranks
  pure newNode

findParent
   : Monad m
  => Node
  -> StateT (S v) m (Maybe Node)
findParent node = do
  MkS _ parents _ _ <- get
  pure $ lookup node parents

setParent
   : Monad m
  => Node
  -> Root
  -> StateT (S v) m ()
setParent node parent = do
  MkS nextNode parents values ranks <- get
  let parents' = insert node parent parents
  put $ MkS nextNode parents' values ranks

findRootImpl
   : Monad m
  => Node
  -> StateT (S v) m Node
findRootImpl node = do
  findParent node >>= \case
    Nothing => do
      -- No parent, so it's a root.
      pure node
    Just parent => do
      root <- findRootImpl parent
      -- Path compression: point directly to the root so the next 'findRoot' is
      -- O(1).
      setParent node root
      pure root

public export
findRoot : Monad m => Node -> UnionFindT v m Node
findRoot node = MkUnionFindT $ do
  findRootImpl node

public export
getValue : Monad m => Node -> UnionFindT v m (Maybe v)
getValue node = MkUnionFindT $ do
  root <- findRootImpl node
  MkS _ _ values _ <- get
  pure $ lookup root values

public export
setValue : Monad m => Node -> Maybe v -> UnionFindT v m ()
setValue node maybeV = MkUnionFindT $ do
  root <- findRootImpl node
  MkS nextNode parents values ranks <- get
  let values' = case maybeV of
                  Just v
                    => insert root v values
                  Nothing
                    => delete root values
  put $ MkS nextNode parents values' ranks

-- When unifying two sets, the caller must specify the new value to associate
-- with the combined set, typically by fetching the values of the two sets and
-- combining them in some way. Note that we do not ask for a function of type
-- `Maybe v -> Maybe v -> Maybe v`, because that would prevent the caller from
-- using side-effects to calculate this function.
public export
union : Monad m => Node -> Node -> Maybe v -> UnionFindT v m ()
union node1 node2 maybeV = MkUnionFindT $ do
  root1 <- findRootImpl node1
  root2 <- findRootImpl node2
  
  if root1 == root2
    then do
      -- Already the same set.
      pure ()
    else do
      MkS nextNode parents values ranks <- get
      -- We have a choice: we could make root1 point to root2, or vice versa.
      -- The "union by rank" optimization is to make the set with the small rank
      -- point to the set with the big rank, to avoid making the big rank even
      -- bigger. If they are the same rank, then we have no choice but to make
      -- that rank bigger.
      let rank1 = fromMaybe 0 $ lookup root1 ranks
          rank2 = fromMaybe 0 $ lookup root2 ranks
          (smallRoot, bigRoot, newBigRank) = 
            if rank1 < rank2
            then (root1, root2, rank2)
            else if rank1 > rank2
            then (root2, root1, rank1)
            else (root2, root1, rank1 + 1)
          parents' = insert smallRoot bigRoot parents
          ranks' = insert bigRoot newBigRank ranks
          values' = delete smallRoot values
          
      -- Next, we assign the new `Maybe v` to the combined set.
      let values'' = case maybeV of
                       Just v => insert bigRoot v values'
                       Nothing => delete bigRoot values'

      put $ MkS nextNode parents' values'' ranks'

----------------------------------------

public export
implementation Monad m => Functor (UnionFindT v m) where
  map f (MkUnionFindT m) = MkUnionFindT $ map f m

public export
implementation Monad m => Applicative (UnionFindT v m) where
  pure x = MkUnionFindT $ pure x
  (MkUnionFindT f) <*> (MkUnionFindT x) = MkUnionFindT $ f <*> x

public export
implementation Monad m => Monad (UnionFindT v m) where
  MkUnionFindT ma >>= f = MkUnionFindT $ ma >>= \a => unUnionFindT (f a)

----------------------------------------

example1 : UnionFind String (List (Maybe String))
example1 = do
  nodeA <- newNode (Just "a")
  nodeB <- newNode (Just "b")
  nodeC <- newNode (Just "c")
  nodeD <- newNode (Just "d")
  nodeE <- newNode (Just "e")

  -- Cheating to get a node which the system doesn't know about.
  -- The fact that the user can technically do this is why the value must be a
  -- Maybe. For unification, this works out because we do want to use Nothing to
  -- represent the case in which we don't know anything about the type
  -- represented by the unification variable.
  let nodeF = nodeE + 1

  union nodeA nodeB (Just "ab")
  union nodeB nodeC (Just "abc")
  setValue nodeC (Just "cba")
  union nodeD nodeE (Just "de")

  valueA <- getValue nodeA
  valueB <- getValue nodeB
  valueC <- getValue nodeC
  valueD <- getValue nodeD
  valueE <- getValue nodeE
  valueF <- getValue nodeF
  pure [valueA, valueB, valueC, valueD, valueE, valueF]

public export
test1 : IO ()
test1 = printLn ( runUnionFind example1
               == [ Just "cba"
                  , Just "cba"
                  , Just "cba"
                  , Just "de"
                  , Just "de"
                  , Nothing
                  ]
                )

----------------------------------------

public export
interface Monad m => MonadUnionFind v m where
  liftUnionFind : UnionFind v a -> m a

public export
implementation Monad m => MonadUnionFind v (UnionFindT v m) where
  liftUnionFind body = MkUnionFindT $ do
    s <- get
    let (s', a) = runState s $ unUnionFindT body
    put s'
    pure a

public export
implementation MonadUnionFind v m => MonadUnionFind v (StateT s m) where
  liftUnionFind body = lift $ liftUnionFind body

public export
implementation MonadUnionFind v m => MonadUnionFind v (ExceptT e m) where
  liftUnionFind body = lift $ liftUnionFind body
