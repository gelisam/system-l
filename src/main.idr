import UTerm.GeneralizeTy
import UTerm.UnifyCtx
import UTerm.UnifyCtxWithLog
import UTerm.UnifyTy
import UTerm.UnionFind
import Examples

----------------------------------------

-- This is my first Idris project and I must admit I don't know how to write
-- tests in this ecosystem. The code GitHub Copilot gave me didn't work, so I
-- wrote my own poor man's test framework. I use the convention that each module
-- exports a number of test<n> functions, which I call here. An example test
-- looks like this:
--
--   test1 : IO ()
--   test1 = printLn ( runUnifyTy example1
--                  == ( Right
--                     $ PImp (UVarTy 0)
--                     $ PImp (UVarTy 0)
--                     $ PImp (UVarTy 0) (UVarTy 1)
--                     )
--                   )
--
-- It should print True if the test passes. I don't check that all the functions
-- return True, I just print True. This way, if it prints False, it is easy to
-- edit the above into the following in order to investigate what's wrong.
--
--   test1 : IO ()
--   test1 = printLn ( runUnifyTy example1
--                   )

main : IO ()
main = do
  putStrLn "typechecks."
  putStr "UnionFind.test1:       "; UnionFind.test1
  putStr "UnifyTy.test1:         "; UnifyTy.test1
  putStr "UnifyTy.test2:         "; UnifyTy.test2
  putStr "UnifyTy.test3:         "; UnifyTy.test3
  putStr "UnifyTy.test4:         "; UnifyTy.test4
  putStr "UnifyTy.test5:         "; UnifyTy.test5
  putStr "GeneralizeTy.test1:    "; GeneralizeTy.test1
  putStr "UnifyCtx.test1:        "; UnifyCtx.test1
  putStr "UnifyCtx.test2:        "; UnifyCtx.test2
  putStr "UnifyCtx.test3:        "; UnifyCtx.test3
  putStr "UnifyCtx.test4:        "; UnifyCtx.test4
  putStr "UnifyCtx.test5:        "; UnifyCtx.test5
  putStr "UnifyCtx.test6:        "; UnifyCtx.test6
  putStr "UnifyCtx.test7:        "; UnifyCtx.test7
  putStr "UnifyCtxWithLog.test1: "; UnifyCtxWithLog.test1
  putStr "UnifyCtxWithLog.test2: "; UnifyCtxWithLog.test2
  putStr "Examples.test1:        "; Examples.test1
  putStr "Examples.test2:        "; Examples.test2
  putStr "Examples.test3:        "; Examples.test3
  putStr "Examples.test4:        "; Examples.test4
  putStr "Examples.test5:        "; Examples.test5
  putStr "Examples.test6:        "; Examples.test6
  putStr "Examples.test7:        "; Examples.test7
  putStr "Examples.test8:        "; Examples.test8
  putStr "Examples.test9:        "; Examples.test9
  putStr "Examples.test10:       "; Examples.test10
  putStrLn "*** tests pass if no False is shown above ***"
