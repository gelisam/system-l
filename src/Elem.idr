-- An index into a context which singles out a single type in a {co,}context.
module Elem

import Ty

----------------------------------------

public export
data Elem : Ty -> List Ty -> Type where
  Here
     : {x : Ty}
    -> {xs : List Ty}
    -> Elem x (x :: xs)
  There
     : {x, y: Ty}
    -> {xs : List Ty}
    -> Elem x xs
    -> Elem x (y :: xs)

public export
allButElem : Elem a g -> List Ty
allButElem (Here {x} {xs})
  = xs
allButElem (There {x} {y} {xs} xElemXs)
  = y :: allButElem xElemXs