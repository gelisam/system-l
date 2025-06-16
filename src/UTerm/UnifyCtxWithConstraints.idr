-- A system for adding constraints on top of the UnifyCtx API, which only
-- supports equality constraints.
--
-- The constraints which can be expressed have the form:
-- * if we know that context A contains variable X...
-- * if we know that context A has these variables...
-- * ...then context B contains variable Y.
-- * ...then context B contains these variables.
-- * .. then this is a contradiction.
--
-- As those are easily expressed via a value of type 'UnifyCtxEventHandler',
-- which reacts to an 'insert' or a 'close' by making further calls to
-- 'UnifyCtxWithLog.insert' and 'UnifyCtxWithLog.close'.
--
-- For example:
-- * context A is a subset of context B
-- * context A and context B are disjoint
-- * context AB is the union of context A and context B
--
-- To implement a system with those extra constraints, create a new monad
-- transformer which wraps UnifyCtxWithConstraintsT and which also remembers the
-- constraints which have been applied so far. In your run function, provide a
-- handler which look at the event, the constraints, and the current state, and
-- make further calls accordingly. Note that the current state is _not_ as it
-- was when the event happened, but as it is now when the handler is running.
-- Other events might have happened in between.
--
-- This delay avoids a common source of bugs where e.g. a handler decides that
-- context A should contain the variables x and y, so it checks that no other
-- variables are present in A, then it calls @insert A x@, @insert A y@, and
-- @close A@. But the @insert A z@ is immediately processed by the handler and
-- via some other constraint it decides to call @insert A z@. At this point, A
-- contains the variables x, y, and z, not just x and y, even though the handler
-- did check that no other variables were present.
module UTerm.UnifyCtxWithConstraints

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.SortedMap as Map

import UTerm.ObserveCtx
import UTerm.PTy
import UTerm.UnifyCtx as UnifyCtx
import UTerm.UnifyCtxWithLog as UnifyCtxWithLog
import UTerm.UnifyTy
import UTerm.UnionFind
import Util.ExceptT
import Util.Map as Map
import Util.MapT
import Util.These

----------------------------------------

public export
UnifyCtxEventHandler : (Type -> Type) -> Type
UnifyCtxEventHandler m
   = UnifyCtxEvent
  -> UnifyCtxWithLogT m ()

private
Impl : (Type -> Type) -> Type -> Type
Impl m = ReaderT (UnifyCtxEventHandler m) (UnifyCtxT m)

public export
record UnifyCtxWithConstraintsT (m : Type -> Type) (a : Type) where
  constructor MkUnifyCtxWithConstraintsT
  unUnifyCtxWithConstraintsT : Impl m a

public export
UnifyCtxWithConstraints : Type -> Type
UnifyCtxWithConstraints = UnifyCtxWithConstraintsT Identity

public export
runUnifyCtxWithConstraintsTWithoutGeneralizing
   : Monad m
  => UnifyCtxEventHandler m
  -> UnifyCtxWithConstraintsT m a
  -> m (Either UnifyCtxError a)
runUnifyCtxWithConstraintsTWithoutGeneralizing handler (MkUnifyCtxWithConstraintsT body) = do
  runUnifyCtxTWithoutGeneralizing $ runReaderT handler body

public export
runUnifyCtxWithConstraintsWithoutGeneralizing
   : UnifyCtxEventHandler Identity
  -> UnifyCtxWithConstraints a
  -> Either UnifyCtxError a
runUnifyCtxWithConstraintsWithoutGeneralizing handler
  = runIdentity . runUnifyCtxWithConstraintsTWithoutGeneralizing handler

----------------------------------------

-- Process all the events: those which are currently in the queue, those which
-- are enqueued as a consequence of processing those events, and so on.
processEventsImpl
   : Monad m
  => UnifyCtxEventHandler m
  -> StateT (List UnifyCtxEvent) (UnifyCtxT m) ()
processEventsImpl handler = do
  get >>= \case
    [] => do
      -- No events to process, stop
      pure ()
    event :: events => do
      put events

      -- Process the event
      runUnifyCtxWithLogT $ handler event  -- Enqueues more events

      -- Keep going
      processEventsImpl handler

-- Similar to Map.insert. Fails if the context is closed.
-- The handler may then trigger additional 'insert' and 'close' calls.
public export
insertImpl
   : Monad m
  => UVarCtx
  -> String
  -> PTy
  -> Impl m ()
insertImpl uvarCtx x pty = do
  previousVars <- liftObserveCtx $ getVarsSoFar uvarCtx

  -- Call the real 'insert'
  lift $ UnifyCtx.insert uvarCtx x pty

  -- If the variable was not already present, trigger the 'Added' event
  case Map.lookup x previousVars of
    Just _ => do
      -- The variable was already there, no event
      pure ()
    Nothing => do
      -- Process the event and all the events it triggers
      handler <- ask
      lift $ evalStateT [Added uvarCtx x] $ do
        processEventsImpl handler

-- Closes a context, preventing further variables from being added.
-- The handler may then trigger additional 'insert' and 'close' calls.
public export
closeImpl
   : Monad m
  => UVarCtx
  -> Impl m ()
closeImpl uvarCtx = do
  wasClosed <- liftObserveCtx $ isClosedUVarCtx uvarCtx

  -- Call the real 'close'
  lift $ UnifyCtx.close uvarCtx

  -- If the context was not already closed, trigger the 'Closed' event
  unless wasClosed $ do
    handler <- ask
    lift $ evalStateT [Closed uvarCtx] $ do
      processEventsImpl handler

----------------------------------------

public export
implementation Monad m => Functor (UnifyCtxWithConstraintsT m) where
  map f (MkUnifyCtxWithConstraintsT m) = MkUnifyCtxWithConstraintsT $ map f m

public export
implementation Monad m => Applicative (UnifyCtxWithConstraintsT m) where
  pure x = MkUnifyCtxWithConstraintsT $ pure x
  MkUnifyCtxWithConstraintsT f <*> MkUnifyCtxWithConstraintsT x
    = MkUnifyCtxWithConstraintsT (f <*> x)

public export
implementation Monad m => Monad (UnifyCtxWithConstraintsT m) where
  (MkUnifyCtxWithConstraintsT ma) >>= f
    = MkUnifyCtxWithConstraintsT $ do
        a <- ma
        unUnifyCtxWithConstraintsT (f a)

public export
implementation MonadTrans UnifyCtxWithConstraintsT where
  lift ma = MkUnifyCtxWithConstraintsT $ lift $ lift ma

-- Note that UnifyCtxWithConstraintsT discharges the MonadObserveCtx constraint,
-- it does _not_ delegate to the m. Being able to observe the contexts is an
-- important part of UnifyCtxWithConstraintsT's API.
public export
implementation Monad m => MonadObserveCtx (UnifyCtxWithConstraintsT m) where
  liftObserveCtx body = MkUnifyCtxWithConstraintsT $ do
    lift $ liftObserveCtx body

-- UnifyCtxWithConstraintsT also discharges the MonadUnifyTy constraint.
public export
implementation Monad m => MonadUnifyTy (UnifyCtxWithConstraintsT m) where
  liftUnifyTy body = MkUnifyCtxWithConstraintsT $ do
    liftUnifyTy body

-- UnifyCtxWithConstraintsT also discharges the MonadUnifyCtx constraint.
-- 'insert' and 'close' are especially important, since this is where the
-- handler is applied. The handler may then trigger additional 'insert' and
-- 'close' calls.
public export
implementation Monad m => MonadUnifyCtx (UnifyCtxWithConstraintsT m) where
  newUVarCtx = MkUnifyCtxWithConstraintsT $ do
    lift newUVarCtx
  insert uvarCtx x pty = MkUnifyCtxWithConstraintsT $ do
    insertImpl uvarCtx x pty
  close uvarCtx = MkUnifyCtxWithConstraintsT $ do
    closeImpl uvarCtx
  unifyUVarCtxs uvarCtx1 uvarCtx2 = MkUnifyCtxWithConstraintsT $ do
    lift $ unifyUVarCtxs uvarCtx1 uvarCtx2

----------------------------------------

-- Example 1: Forbid reserved keywords (like "if") as variable names in any
-- context

UnifyCtxWithKeywords : Type -> Type
UnifyCtxWithKeywords = UnifyCtxWithConstraintsT (Except String)

-- Throw an error if a reserved keyword is added as a variable
keywordHandler
   : UnifyCtxEventHandler (Except String)
keywordHandler (Added _ "if") = do
    lift $ throwE ("'if' is a reserved keyword")
keywordHandler _ = do
  pure ()

runUnifyCtxWithKeywords
   : UnifyCtxWithKeywords a
  -> Either String (Either UnifyCtxError a)
runUnifyCtxWithKeywords
  = runExcept
  . runUnifyCtxWithConstraintsTWithoutGeneralizing keywordHandler

example1
   : UnifyCtxWithKeywords (Map String PTy)
example1 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarCtx1 <- newOpenUVarCtx $ Map.fromList [ ("if", uvarTy0) ]
  liftObserveCtx $ getVarsSoFar uvarCtx1

public export
test1 : IO ()
test1 = printLn ( runUnifyCtxWithKeywords example1
               == Left "'if' is a reserved keyword"
                )

----------------------------------------

-- Example 2: context 0 is a subset of context 1

UnifyCtxWithSubset : Type -> Type
UnifyCtxWithSubset = UnifyCtxWithConstraints

-- Since context 0 is a subset of context 1, any variable in context 0 must also
-- be in context 1.
copyVarTo1
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> String
  -> UnifyCtxWithLogT m ()
copyVarTo1 context0 context1 x = do
  -- Check if the variable is in context 0
  vars0 <- liftObserveCtx $ getVarsSoFar context0
  whenJust (Map.lookup x vars0) $ \pty => do
    -- The variable is in context 0, so it must also be in context 1
    insert context1 x pty

-- More subtly, if context 1 is closed and has the same variables as context 0,
-- then we know that no more variables can be added to context 0 without
-- breaking the invariant that context 0 is a subset of context 1, so we can
-- close context 0.
close0IfNeeded
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> UnifyCtxWithLogT m ()
close0IfNeeded context0 context1 = do
  isClosed0 <- liftObserveCtx $ isClosedUVarCtx context0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
  case (isClosed0, isClosed1) of
    (_, False) => do
      -- Context 1 is still open, nothing to conclude
      pure ()
    (True, _) => do
      -- Context 0 is closed, so there will be nothing to do if we conclude that
      -- we can close context 0
      pure ()
    (False, True) => do
      vars0 <- liftObserveCtx $ getVarsSoFar context0
      vars1 <- liftObserveCtx $ getVarsSoFar context1

      -- Since the other handler checks ensure that the variables of context 0
      -- are a subset of the variables of context 1, it suffices to check the
      -- lengths to conclude that they are the same sets of variables.
      let len0 = length $ Map.toList vars0
      let len1 = length $ Map.toList vars1
      when (len0 == len1) $ do
        close context0

-- Handler that implements the subset constraint:
-- * When variables are added to context 0, also add them to context 1
-- * If context 1 is closed and both contexts have the same variables, close context 0
public export
subsetHandler
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> UnifyCtxEventHandler m
subsetHandler subset0 subset1 (Added _ x) = do
  copyVarTo1 subset0 subset1 x
  close0IfNeeded subset0 subset1
subsetHandler subset0 subset1 (Closed _) = do
  close0IfNeeded subset0 subset1

runUnifyCtxWithSubset
   : UnifyCtxWithSubset a
  -> Either UnifyCtxError a
runUnifyCtxWithSubset
  = runUnifyCtxWithConstraintsWithoutGeneralizing (subsetHandler (MkNode 0) (MkNode 1))

example2
   : UnifyCtxWithSubset ((Bool, Map String PTy), (Bool, Map String PTy))
example2 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx  -- This will be MkNode 0
  uvarCtx1 <- newUVarCtx  -- This will be MkNode 1

  -- Add a variable to context 0 (should trigger adding to context 1)
  insert uvarCtx0 "x" uvarTy0

  -- Add another variable to context 1 directly
  insert uvarCtx1 "y" uvarTy1

  -- Add the same variable to context 0 (should unify uvarTy1 and uvarTy2)
  insert uvarCtx0 "y" uvarTy2

  -- Close context 1 (should trigger closing context 0)
  close uvarCtx1

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  pure ((isClosed0, vars0), (isClosed1, vars1))

public export
test2 : IO ()
test2 = printLn ( runUnifyCtxWithSubset example2
               == Right ( (True, Map.fromList [("x", UVarTy (MkNode 0)), ("y", (UVarTy (MkNode 1)))])
                        , (True, Map.fromList [("x", UVarTy (MkNode 0)), ("y", (UVarTy (MkNode 1)))])
                        )
                )

-- Same as example2 but in a different order
example3
   : UnifyCtxWithSubset ((Bool, Map String PTy), (Bool, Map String PTy))
example3 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx  -- This will be MkNode 0
  uvarCtx1 <- newUVarCtx  -- This will be MkNode 1

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  -- Close context 1. This does _not_ trigger closing context 0, since
  -- we don't yet know whether context 0 contains "y" or not.
  close uvarCtx1

  -- Add "y" to context 0. Now contexts 0 and 1 have the same variables, so this
  -- should trigger closing context 0.
  insert uvarCtx0 "y" uvarTy2

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  pure ((isClosed0, vars0), (isClosed1, vars1))

public export
test3 : IO ()
test3 = printLn ( runUnifyCtxWithSubset example3
               == Right ( (True, Map.fromList [("x", UVarTy (MkNode 0)), ("y", (UVarTy (MkNode 1)))])
                        , (True, Map.fromList [("x", UVarTy (MkNode 0)), ("y", (UVarTy (MkNode 1)))])
                        )
                )

----------------------------------------

-- Example 3: context 0 and context 1 are disjoint

UnifyCtxWithDisjoint : Type -> Type
UnifyCtxWithDisjoint = UnifyCtxWithConstraintsT (Except String)

-- A variable should not be in both contexts.
public export
disjointHandler
   : MonadExcept e m
  => UVarCtx
  -> UVarCtx
  -> (String -> e)
  -> UnifyCtxEventHandler m
disjointHandler context0 context1 mkError (Added ctx x) = do
  when (ctx == context0) $ do
    -- Variable added to context 0, check if it exists in context 1
    vars1 <- liftObserveCtx $ getVarsSoFar context1
    whenJust (Map.lookup x vars1) $ \_ => do
      lift $ liftExcept $ throwE $ mkError x
  when (ctx == context1) $ do
    -- Variable added to context 1, check if it exists in context 0
    vars0 <- liftObserveCtx $ getVarsSoFar context0
    whenJust (Map.lookup x vars0) $ \_ => do
      lift $ liftExcept $ throwE $ mkError x
disjointHandler _ _ _ (Closed _) = do
  pure ()

runUnifyCtxWithDisjoint
   : UnifyCtxWithDisjoint a
  -> Either String (Either UnifyCtxError a)
runUnifyCtxWithDisjoint
  = runExcept
  . runUnifyCtxWithConstraintsTWithoutGeneralizing handler
  where
    mkError : String -> String
    mkError x = "Variable '" ++ x ++ "' is in both context 0 and context 1"

    handler : UnifyCtxEventHandler (Except String)
    handler = disjointHandler (MkNode 0) (MkNode 1) mkError

-- Add a different variable to each context (should be accepted)
example4
   : UnifyCtxWithDisjoint ((Bool, Map String PTy), (Bool, Map String PTy))
example4 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx  -- This will be MkNode 0
  uvarCtx1 <- newUVarCtx  -- This will be MkNode 1

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  pure ((isClosed0, vars0), (isClosed1, vars1))

public export
test4 : IO ()
test4 = printLn ( runUnifyCtxWithDisjoint example4
               == ( Right
                  $ Right ( (False, Map.fromList [("x", UVarTy (MkNode 0))])
                          , (False, Map.fromList [("y", UVarTy (MkNode 1))])
                          )
                  )
                )

-- Add the same variable to both contexts (should be rejected)
example5
   : UnifyCtxWithDisjoint ((Bool, Map String PTy), (Bool, Map String PTy))
example5 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx  -- This will be MkNode 0
  uvarCtx1 <- newUVarCtx  -- This will be MkNode 1

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "x" uvarTy1

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  pure ((isClosed0, vars0), (isClosed1, vars1))

public export
test5 : IO ()
test5 = printLn ( runUnifyCtxWithDisjoint example5
               == Left "Variable 'x' is in both context 0 and context 1"
                )

----------------------------------------

-- Example 4: context 2 is the disjoint union of context 0 and context 1

UnifyCtxWithDisjointUnion : Type -> Type
UnifyCtxWithDisjointUnion = UnifyCtxWithConstraintsT (Except String)

-- There are a lot of cases to consider, so let's be systematic by considering
-- all the possibilities about which contexts are closed and to which context
-- the variable was added.
--
-- * 2 open,   1 open,   0 open,   add to context 0: also add to 2 ('subsetHandler')
-- * 2 open,   1 open,   0 open,   add to context 1: also add to 2 ('subsetHandler')
-- * 2 open,   1 open,   0 open,   add to context 2: could come from 0 or 1, too soon to tell
-- * 2 open,   1 open,   0 closed, just closed:      now we can tell they came from 1 ('subtractContexts')
-- * 2 open,   1 open,   0 closed, add to context 1: also add to 2 ('subsetHandler')
-- * 2 open,   1 open,   0 closed, add to context 2: must come from 1 ('subtractContexts')
-- * 2 open,   1 closed, 0 open,   just closed:      now we can tell they came from 0 ('subtractContexts')
-- * 2 open,   1 closed, 0 open,   add to context 0: also add to 2 ('subsetHandler')
-- * 2 open,   1 closed, 0 open,   add to context 2: must come from 0 ('subtractContexts')
-- * 2 open,   1 closed, 0 closed, just closed:      close 2 as well ('sumContexts')
-- * 2 open,   1 closed, 0 closed, add to context 2: can't come from 0 nor 1, error ('sumContexts')
-- * 2 closed, 1 open,   0 open,   just closed:      still too soon to tell
-- * 2 closed, 1 open,   0 open,   add to context 0: also add to 2 ('subsetHandler')
-- * 2 closed, 1 open,   0 open,   add to context 1: also add to 2 ('subsetHandler')
-- * 2 closed, 1 open,   0 closed, just closed:      also close 1 ('subtractContexts')
-- * 2 closed, 1 open,   0 closed, add to context 1: can't add anymore, error ('subsetHandler')
-- * 2 closed, 1 closed, 0 open,   just closed:      also close 0 ('subtractContexts')
-- * 2 closed, 1 closed, 0 open,   add to context 0: can't add anymore, error ('subsetHandler')
-- * 2 closed, 1 closed, 0 closed, just closed:      one last check that everything lines up ('verifyContexts')

-- Context 2 minus context 1 equals context 0. If context 1 is closed, then any
-- variable added to context 2 must come from context 0. If context 2 is also
-- closed, then we can close context 0.
subtractContexts
   : Monad m
  => UVarCtx
  -> UVarCtx
  -> UVarCtx
  -> UnifyCtxEventHandler m
subtractContexts context2 context1 context0 (Added ctx x) = do
  when (ctx == context2) $ do
    isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
    when isClosed1 $ do
      -- Context 1 is closed, so any variable added to context 2 must come from
      -- context 0.
      vars2 <- liftObserveCtx $ getVarsSoFar context2
      whenJust (Map.lookup x vars2) $ \pty => do
        insert context0 x pty
subtractContexts context2 context1 context0 (Closed ctx) = do
  when (ctx == context1) $ do
    -- Context 1 is closed, so any variables which were previously added to
    -- context 2 (but not context 1) must come from context 0.
    vars2 <- liftObserveCtx $ getVarsSoFar context2
    vars1 <- liftObserveCtx $ getVarsSoFar context1
    let mustBeIn0 = Map.difference vars2 vars1
    sequence_ $ withKey $ flip map mustBeIn0 $ \pty, x => do
      insert context0 x pty

  when (ctx == context2 || ctx == context1) $ do
    isClosed2 <- liftObserveCtx $ isClosedUVarCtx context2
    isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
    when (isClosed2 && isClosed1) $ do
      -- Contexts 2 and 1 are both closed, so no more variables can be added to
      -- context 0.
      close context0

-- If contexts 0 and 1 are both closed, then
-- * no more variables can be added to context 2
-- * context 2 can be closed
sumContexts
   : MonadExcept e m
  => UVarCtx
  -> UVarCtx
  -> UVarCtx
  -> (String -> e)
  -> UnifyCtxEventHandler m
sumContexts context0 context1 context2 only2 (Added ctx x) = do
  when (ctx == context2) $ do
    isClosed0 <- liftObserveCtx $ isClosedUVarCtx context0
    isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
    when (isClosed0 && isClosed1) $ do
      -- Contexts 0 and 1 are both closed, so we cannot add any more variables
      -- to context 2.
      lift $ liftExcept $ throwE $ only2 x
sumContexts context0 context1 context2 _ (Closed ctx) = do
  when (ctx == context0 || ctx == context1) $ do
    isClosed0 <- liftObserveCtx $ isClosedUVarCtx context0
    isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
    when (isClosed0 && isClosed1) $ do
      -- Contexts 0 and 1 are both closed, so no more variables can be added
      -- to context 2. Close it as well.
      close context2

verifyContexts
   : MonadExcept e m
  => UVarCtx
  -> UVarCtx
  -> UVarCtx
  -> (String -> e)
  -> (String -> e)
  -> (String -> e)
  -> (String -> e)
  -> UnifyCtxEventHandler m
verifyContexts _ _ _ _ _ _ _ (Added _ _) = do
  pure ()
verifyContexts context0 context1 context2 only0 only1 only2 both01 (Closed ctx) = do
  when (ctx == context0 || ctx == context1 || ctx == context2) $ do
    isClosed0 <- liftObserveCtx $ isClosedUVarCtx context0
    isClosed1 <- liftObserveCtx $ isClosedUVarCtx context1
    isClosed2 <- liftObserveCtx $ isClosedUVarCtx context2
    when (isClosed0 && isClosed1 && isClosed2) $ do
      -- All three contexts are closed, double-check that context 2 is the
      -- disjoint union of contexts 0 and 1.
      vars0 <- liftObserveCtx $ getVarsSoFar context0
      vars1 <- liftObserveCtx $ getVarsSoFar context1
      vars2 <- liftObserveCtx $ getVarsSoFar context2
      sequence_ $ withKey $ Map.union (Map.union vars0 vars1 id) vars2 $ \case
        This (This _) => \x => do
          -- Variable is only in context 0. Not good.
          lift $ liftExcept $ throwE $ only0 x
        This (That _) => \x => do
          -- Variable is only in context 1. Not good.
          lift $ liftExcept $ throwE $ only1 x
        This (Both _ _) => \x => do
          -- Variable is in both context 0 and context 1. Not good.
          lift $ liftExcept $ throwE $ both01 x
        That _ => \x => do
          -- Variable is only in context 2. Not good.
          lift $ liftExcept $ throwE $ only2 x
        Both (This _) _ => \_ => do
          -- Variable is in context 0 and context2, but not in context 1. Good.
          pure ()
        Both (That _) _ => \_ => do
          -- Variable is in context 1 and context2, but not in context 0. Good.
          pure ()
        Both (Both _ _) _ => \x => do
          -- Variable is in both context 0 and context 1. Not good.
          lift $ liftExcept $ throwE $ both01 x

public export
disjointUnionHandler
   : MonadExcept e m
  => UVarCtx
  -> UVarCtx
  -> UVarCtx
  -> (String -> e)
  -> (String -> e)
  -> (String -> e)
  -> (String -> e)
  -> UnifyCtxEventHandler m
disjointUnionHandler context0 context1 context2 only0 only1 only2 both01 event = do
  disjointHandler context0 context1 both01 event
  subsetHandler context0 context2 event
  subsetHandler context1 context2 event
  subtractContexts context2 context0 context1 event
  subtractContexts context2 context1 context0 event
  sumContexts context0 context1 context2 only2 event
  verifyContexts context0 context1 context2 only0 only1 only2 both01 event

runUnifyCtxWithDisjointUnion
   : UnifyCtxWithDisjointUnion a
  -> Either String (Either UnifyCtxError a)
runUnifyCtxWithDisjointUnion
  = runExcept
  . runUnifyCtxWithConstraintsTWithoutGeneralizing handler
  where
    only0 : String -> String
    only0 x = "Variable '" ++ x ++ "' is in context 0 but not in context 2, which should be a superset."

    only1 : String -> String
    only1 x = "Variable '" ++ x ++ "' is in context 1 but not in context 2, which should be a superset."

    only2 : String -> String
    only2 x = "Variable '" ++ x ++ "' is in context 2, which should be the disjoint union of contexts 0 and 1, but that variable does not appear in either."

    both01 : String -> String
    both01 x = "Variable '" ++ x ++ "' is in both context 0 and context 1, which should be disjoint."

    handler : UnifyCtxEventHandler (Except String)
    handler = disjointUnionHandler (MkNode 0) (MkNode 1) (MkNode 2) only0 only1 only2 both01

example6
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example6 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx  -- This will be MkNode 0
  uvarCtx1 <- newUVarCtx  -- This will be MkNode 1
  uvarCtx2 <- newUVarCtx  -- This will be MkNode 2

  -- Add variables to contexts 0 and 1 (should automatically appear in 2)
  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  -- Close contexts 0
  close uvarCtx0

  -- Add variable to context 2 (should automatically appear in 1 since 0 is closed)
  insert uvarCtx2 "z" uvarTy2

  -- Close context 1 (should automatically close 2)
  close uvarCtx1

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test6 : IO ()
test6 = printLn ( runUnifyCtxWithDisjointUnion example6
               == ( Right
                  $ Right
                      ( (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            ])
                      , (True, Map.fromList [ ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      , (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            , ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      )
                  )
                )

-- Same as test6 but with a different order
example7
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example7 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx
  uvarCtx1 <- newUVarCtx
  uvarCtx2 <- newUVarCtx

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  -- test6 was closing 0 before inserting into 2
  insert uvarCtx2 "z" uvarTy2

  -- Close context 0 (should automatically add "z" to 1 since we now know it can't be in 0)
  close uvarCtx0

  -- test6 was closing context 1
  -- Closed context 2 (should automatically close 1 since all variables are accounted for)
  close uvarCtx2

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test7 : IO ()
test7 = printLn ( runUnifyCtxWithDisjointUnion example7
               == ( Right
                  $ Right
                      ( (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            ])
                      , (True, Map.fromList [ ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      , (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            , ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      )
                  )
                )

-- Same as test7 but with yet another order
example8
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example8 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx
  uvarCtx1 <- newUVarCtx
  uvarCtx2 <- newUVarCtx

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1
  insert uvarCtx2 "z" uvarTy2

  -- test7 was closing 0 before closing 2
  close uvarCtx2

  -- Close context 0 (should automatically add "z" to context 1 and close it)
  close uvarCtx0

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test8 : IO ()
test8 = printLn ( runUnifyCtxWithDisjointUnion example8
               == ( Right
                  $ Right
                      ( (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            ])
                      , (True, Map.fromList [ ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      , (True, Map.fromList [ ("x", UVarTy (MkNode 0))
                                            , ("y", UVarTy (MkNode 1))
                                            , ("z", UVarTy (MkNode 2))
                                            ])
                      )
                  )
                )

-- Test case 9: Try to add to context 2 when both 0 and 1 are closed (should fail)
example9
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example9 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx
  uvarCtx1 <- newUVarCtx
  uvarCtx2 <- newUVarCtx

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  -- Close both contexts 0 and 1 (automatically closes context 2)
  close uvarCtx0
  close uvarCtx1

  -- Now try to add a new variable to context 2 (should fail since 2 is closed)
  insert uvarCtx2 "z" uvarTy2

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test9 : IO ()
test9 = printLn ( runUnifyCtxWithDisjointUnion example9
               == Right (Left (VariableAddedToClosedContext "z" (MkNode 2)))
                )

-- Test case 10: Try to add to context 0 when context 2 is already closed (should fail)
example10
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example10 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy
  uvarTy2 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx
  uvarCtx1 <- newUVarCtx
  uvarCtx2 <- newUVarCtx

  insert uvarCtx0 "x" uvarTy0
  insert uvarCtx1 "y" uvarTy1

  -- Close context 2 first
  close uvarCtx2

  -- Now try to add a new variable to context 0 (should automatically add "z" to
  -- context 2, which should fail since 2 is closed)
  insert uvarCtx0 "z" uvarTy2

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test10 : IO ()
test10 = printLn ( runUnifyCtxWithDisjointUnion example9
                == Right (Left (VariableAddedToClosedContext "z" (MkNode 2)))
                 )

-- Test case 11: Try to add the same variable to both contexts 0 and 1 (should fail)
example11
   : UnifyCtxWithDisjointUnion ((Bool, Map String PTy), (Bool, Map String PTy), (Bool, Map String PTy))
example11 = do
  uvarTy0 <- liftUnifyTy newUVarTy
  uvarTy1 <- liftUnifyTy newUVarTy

  uvarCtx0 <- newUVarCtx
  uvarCtx1 <- newUVarCtx
  uvarCtx2 <- newUVarCtx

  -- Add a variable to context 0
  insert uvarCtx0 "x" uvarTy0

  -- Add the same variable to context 1 (should fail since contexts are disjoint)
  insert uvarCtx1 "x" uvarTy1

  isClosed0 <- liftObserveCtx $ isClosedUVarCtx uvarCtx0
  isClosed1 <- liftObserveCtx $ isClosedUVarCtx uvarCtx1
  isClosed2 <- liftObserveCtx $ isClosedUVarCtx uvarCtx2
  vars0 <- liftObserveCtx $ zonkUVarCtx uvarCtx0
  vars1 <- liftObserveCtx $ zonkUVarCtx uvarCtx1
  vars2 <- liftObserveCtx $ zonkUVarCtx uvarCtx2
  pure ((isClosed0, vars0), (isClosed1, vars1), (isClosed2, vars2))

public export
test11 : IO ()
test11 = printLn ( runUnifyCtxWithDisjointUnion example11
                == Left "Variable 'x' is in both context 0 and context 1, which should be disjoint."
                 )
