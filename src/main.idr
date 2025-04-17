import UnionFind
import UnifyTy
import Generalize
import Examples

----------------------------------------

main : IO ()
main = do
  putStrLn "typechecks."
  UnionFind.test1
  UnifyTy.test1
  UnifyTy.test2
  UnifyTy.test3
  Generalize.test1
  Examples.test1
  putStrLn "*** tests pass if no False is shown above ***"
