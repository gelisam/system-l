module ExceptT


public export
data ExceptT : (e : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkExceptT : m (Either e a) -> ExceptT e m a

public export
runExceptT : ExceptT e m a -> m (Either e a)
runExceptT (MkExceptT body) = body

public export
throwE : Monad m => e -> ExceptT e m a
throwE e = MkExceptT $ do
  pure $ Left e

public export
lift : Monad m => m a -> ExceptT e m a
lift body = MkExceptT $ do
  a <- body
  pure $ Right a

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
