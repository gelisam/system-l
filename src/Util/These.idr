-- A variant of (Maybe a, Maybe b) where the (Nothing, Nothing) case is
-- unrepresentable.
module Util.These

----------------------------------------

public export
data These a b = This a | That b | Both a b

public export
mapBoth
   : (a -> a')
  -> (b -> b')
  -> These a b
  -> These a' b'
mapBoth f g (This a)
  = This (f a)
mapBoth _ g (That b)
  = That (g b)
mapBoth f g (Both a b)
  = Both (f a) (g b)

public export
mapThis
   : (a -> a')
  -> These a b
  -> These a' b
mapThis f = mapBoth f id

public export
mapThat
   : (b -> b')
  -> These a b
  -> These a b'
mapThat f = mapBoth id f

public export
getThis
   : These a b
  -> Maybe a
getThis (This a)
  = Just a
getThis (That _)
  = Nothing
getThis (Both a _)
  = Just a

public export
getThat
   : These a b
  -> Maybe b
getThat (This _)
  = Nothing
getThat (That b)
  = Just b
getThat (Both _ b)
  = Just b

-----------------------------------------

public export
implementation (Show a, Show b) => Show (These a b) where
  showPrec p (This a)
    = showParens (p /= Open)
    $ "This " ++ showPrec App a
  showPrec p (That b)
    = showParens (p /= Open)
    $ "That " ++ showPrec App b
  showPrec p (Both a b)
    = showParens (p /= Open)
    $ "Both " ++ showPrec App a ++ " " ++ showPrec App b

public export
implementation (Eq a, Eq b) => Eq (These a b) where
  This a1 == This a2
    = a1 == a2
  That b1 == That b2
    = b1 == b2
  Both a1 b1 == Both a2 b2
    = a1 == a2
   && b1 == b2
  _ == _
    = False