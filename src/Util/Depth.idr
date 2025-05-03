module Util.Depth

public export
data Depth
  = Infinite
  | Finite Nat

public export
decrDepth : Depth -> Depth
decrDepth Infinite
  = Infinite
decrDepth (Finite Z)
  = Finite Z
decrDepth (Finite (S n))
  = Finite n