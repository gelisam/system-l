module UnionFind

import Data.Maybe
import Data.SortedMap
import Control.Monad.State


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

-- UnionFind state monad for easier manipulation.
public export
UnionFind : Type -> Type -> Type
UnionFind v a = State (S v) a

public export
runUF : UnionFind v a -> a
runUF = evalState (MkS 0 empty empty empty)

public export
newNode : Maybe v -> UnionFind v Node
newNode maybeV = do
  MkS newNode parents values ranks <- get
  let values' = case maybeV of
                  Just v
                    => insert newNode v values
                  Nothing
                    => values
  put $ MkS (newNode + 1) parents values' ranks
  pure newNode

findParent : Node -> UnionFind v (Maybe Node)
findParent node = do
  MkS _ parents _ _ <- get
  pure $ lookup node parents

setParent : Node -> Root -> UnionFind v ()
setParent node parent = do
  MkS nextNode parents values ranks <- get
  let parents' = insert node parent parents
  put $ MkS nextNode parents values ranks

public export
findRoot : Node -> UnionFind v Node
findRoot node = do
  findParent node >>= \case
    Nothing => do
      -- No parent, so it's a root.
      pure node
    Just parent => do
      root <- findRoot parent
      -- Path compression: point directly to the root so the next 'findRoot' is
      -- O(1).
      setParent node root
      pure root

public export
getValue : Node -> UnionFind v (Maybe v)
getValue node = do
  root <- findRoot node
  MkS _ _ values _ <- get
  pure $ lookup root values

public export
setValue : Node -> Maybe v -> UnionFind v ()
setValue node maybeV = do
  root <- findRoot node
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
union : Node -> Node -> Maybe v -> UnionFind v ()
union node1 node2 maybeV = do
  root1 <- findRoot node1
  root2 <- findRoot node2
  
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
