import UTerm.GeneralizeTy
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
--                     $ PImp (MetaVar 0)
--                     $ PImp (MetaVar 0)
--                     $ PImp (MetaVar 0) (MetaVar 1)
--                     )
--                   )
--
-- It should print True if the test passes. If it prints False, it is easy to
-- edit the above into the following in order to investigate what's wrong.
--
--   test1 : IO ()
--   test1 = printLn ( runUnifyTy example1
--                   )

main : IO ()
main = do
  putStrLn "typechecks."
  UnionFind.test1
  UnifyTy.test1
  UnifyTy.test2
  UnifyTy.test3
  GeneralizeTy.test1
  Examples.test1
  putStrLn "*** tests pass if no False is shown above ***"
