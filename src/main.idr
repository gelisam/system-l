import UTerm.GeneralizeTy
import UTerm.UnifyExtensible
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
  putStr "UnifyExtensible.test1: "; UnifyExtensible.test1
  putStr "UnifyTy.test1:         "; UnifyTy.test1
  putStr "UnifyTy.test2:         "; UnifyTy.test2
  putStr "UnifyTy.test3:         "; UnifyTy.test3
  putStr "UnifyTy.test4:         "; UnifyTy.test4
  putStr "UnifyTy.test5:         "; UnifyTy.test5
  putStr "GeneralizeTy.test1:    "; GeneralizeTy.test1
  putStr "Examples.test1:        "; Examples.test1
  putStrLn "*** tests pass if no False is shown above ***"
