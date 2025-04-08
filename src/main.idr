import UnionFind
import Unification

main : IO ()
main = do
  putStrLn "typechecks."
  UnionFind.test1
  Unification.test1
  Unification.test2
  Unification.test3
  putStrLn "*** ALL TESTS PASSED ***"
