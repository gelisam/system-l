module Util.MapT

import Control.Monad.Reader
import Control.Monad.State

public export
interface MapT (t : (Type -> Type) -> Type -> Type) where
  mapT
     : (Monad m1, Monad m2)
    => (forall x. m1 x -> m2 x)
    -> t m1 a -> t m2 a

public export
implementation {r : Type} -> MapT (ReaderT r) where
  mapT f body = do
    r <- ask
    lift $ f $ runReaderT r body

public export
implementation {s : Type} -> MapT (StateT s) where
  mapT f body = do
    s <- get
    (s', a) <- lift $ f $ runStateT s body
    put s'
    pure a
