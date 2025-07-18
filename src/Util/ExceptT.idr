-- A standard monad transformer for throwing errors.
--
-- This is my first Idris project and I don't know why StateT is built-in but
-- ExceptT is not. I couldn't figure out how to obtain ExceptT from Idris's
-- equivalent of hackage, so I wrote my own.
module Util.ExceptT

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans

import Util.MapT

----------------------------------------

public export
data ExceptT : (e : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkExceptT : m (Either e a) -> ExceptT e m a

public export
Except : Type -> Type -> Type
Except e = ExceptT e Identity

public export
runExceptT : ExceptT e m a -> m (Either e a)
runExceptT (MkExceptT body) = body

public export
runExcept : Except e a -> Either e a
runExcept = runIdentity . runExceptT

public export
throwE : Monad m => e -> ExceptT e m a
throwE e = MkExceptT $ do
  pure $ Left e

----------------------------------------

public export
implementation Functor m => Functor (ExceptT e m) where
  map f (MkExceptT body) = MkExceptT (map (map f) body)

public export
implementation Monad m => Applicative (ExceptT e m) where
  pure x = MkExceptT (pure (Right x))
  (MkExceptT bodyF) <*> (MkExceptT bodyA) = MkExceptT $ do
    bodyF >>= \case
      Left err => do
        pure $ Left err
      Right f => do
        bodyA >>= \case
          Left err => do
            pure $ Left err
          Right a => do
            pure $ Right $ f a

public export
implementation Monad m => Monad (ExceptT e m) where
  (MkExceptT body) >>= k = MkExceptT $ do
    body >>= \case
      Left err => do
        pure $ Left err
      Right a => do
        runExceptT $ k a

public export
implementation MonadTrans (ExceptT e) where
  lift body = MkExceptT $ do
    a <- body
    pure $ Right a

public export
implementation {e : Type} -> MapT (ExceptT e) where
  mapT f (MkExceptT body) = MkExceptT (f body)

----------------------------------------

public export
interface Monad m => MonadExcept e m where
  liftExcept : Except e a -> m a

public export
implementation Monad m => MonadExcept e (ExceptT e m) where
  liftExcept body = MkExceptT $ do
    case runExcept body of
      Left e => do
        pure $ Left e
      Right a => do
        pure $ Right a

public export
implementation MonadExcept e m => MonadExcept e (StateT s m) where
  liftExcept = lift . liftExcept

public export
implementation MonadExcept e m => MonadExcept e (ReaderT r m) where
  liftExcept body = lift $ liftExcept body
