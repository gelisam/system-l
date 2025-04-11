module Cover

import Elem
import Ty

----------------------------------------

-- `Cover g d gd` is a proof that `gd` can be partitioned into `g` and `d`. The
-- order is preserved but isn't that important since in System L it is possible
-- to construct a term which swaps variables.
public export
data Cover : List Ty -> List Ty -> List Ty -> Type where
  Nil
     : Cover [] [] []
  PickLeft
     : Cover g d gd
    -> Cover (a::g) d (a::gd)
  PickRight
     : Cover g d gd
    -> Cover g (a::d) (a::gd)

public export
allLeft
   : {g : List Ty}
  -> Cover g [] g
allLeft {g = []}
  = Nil
allLeft {g = a :: g}
  = PickLeft (allLeft {g})

public export
allRight
   : {d : List Ty}
  -> Cover [] d d
allRight {d = []}
  = Nil
allRight {d = a :: d}
  = PickRight (allRight {d})

public export
pickLeftFromElem
   : (xElemXs : Elem x xs)
  -> Cover [x] (allButElem xElemXs) xs
pickLeftFromElem Here
  = PickLeft allRight
pickLeftFromElem (There xElemXs)
  = PickRight (pickLeftFromElem xElemXs)

public export
pickRightFromElem
   : (xElemXs : Elem x xs)
  -> Cover (allButElem xElemXs) [x] xs
pickRightFromElem Here
  = PickRight allLeft
pickRightFromElem (There xElemXs)
  = PickLeft (pickRightFromElem xElemXs)

public export
flipCover
   : Cover g g' gg'
  -> Cover g' g gg'
flipCover Nil
  = Nil
flipCover (PickLeft cover)
  = PickRight (flipCover cover)
flipCover (PickRight cover)
  = PickLeft (flipCover cover)