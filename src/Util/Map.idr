-- Extra functions for working with SortedMap.
module Util.Map

import Data.List as List
import Data.SortedMap as Map

import Util.These

----------------------------------------

public export
Map : Type -> Type -> Type
Map = SortedMap

public export
withKey
   : Ord k
  => Map k (k -> v)
  -> Map k v
withKey
  = Map.fromList
  . map (\(k, f) => (k, f k))
  . Map.toList


public export
filterJust
   : Ord k
  => Map k (Maybe v)
  -> Map k v
filterJust
  = Map.fromList
  . List.catMaybes
  . map sequence
  . Map.toList

public export
union
   : Ord k
  => Map k v1
  -> Map k v2
  -> (These v1 v2 -> v3)
  -> Map k v3
union v1s v2s f
  = map (\(_, _, v3) => v3) maybes3
  where
    f1 : v1 -> (Maybe v1, Maybe v2, v3)
    f1 v1 = (Just v1, Nothing, f (This v1))

    f2 : v2 -> (Maybe v1, Maybe v2, v3)
    f2 v2 = (Nothing, Just v2, f (That v2))

    f' : (Maybe v1, Maybe v2, v3)
      -> (Maybe v1, Maybe v2, v3)
      -> (Maybe v1, Maybe v2, v3)
    f' (Just v1, Nothing, _) (Nothing, Just v2, _)
      = (Nothing, Nothing, f (Both v1 v2))
    f' (_, _, v3) (_, _, _)
      = -- never happens
        (Nothing, Nothing, v3)

    maybes1 : Map k (Maybe v1, Maybe v2, v3)
    maybes1 = map f1 v1s
    
    maybes2 : Map k (Maybe v1, Maybe v2, v3)
    maybes2 = map f2 v2s
    
    maybes3 : Map k (Maybe v1, Maybe v2, v3)
    maybes3 = Map.mergeWith f' maybes1 maybes2

public export
intersection
   : Ord k
  => Map k v1
  -> Map k v2
  -> (v1 -> v2 -> v3)
  -> Map k v3
intersection v1s v2s f
  = filterJust $ union v1s v2s $ \case
      (This _)
        => Nothing
      (That _)
        => Nothing
      (Both v1 v2)
        => Just (f v1 v2)

public export
difference
   : Ord k
  => Map k v
  -> Map k x
  -> Map k v
difference vs xs
  = filterJust $ union vs xs $ \case
      (This v)
        => Just v
      (That _)
        => Nothing
      (Both _ _)
        => Nothing