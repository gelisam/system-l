import UnionFind
import Unification
import Examples

main : IO ()
main = do
  putStrLn "typechecks."
  UnionFind.test1
  Unification.test1
  Unification.test2
  Unification.test3
  Examples.test1
  putStrLn "*** tests pass if no False is shown above ***"
