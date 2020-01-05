module TestEx

import Control.App
import Control.App.Console

namespace StateEx
  public export
  interface Console e => StateEx e where
    inc : App e Int
    testRes : String -> App e Bool

  export
  Has [Console, State Int, Exception String] e => StateEx e where
    inc
        = do count <- get
             put (count + the Int 1)
             pure count

    testRes str
        = do count <- get
             case str of
                  "DONE" => pure True
                  "BAD" => throw "Nope"
                  _ => do putStrLn $ "Hello " ++ str ++ " " ++ show count
                          pure False

test : Has [StateEx] e => App e ()
test
    = do putStr "Name: "
         inc
         x <- getStr
         done <- testRes x
         if done
            then pure ()
            else test

blarg : Has [Console, StateEx] e => App e ()
blarg
    = do new "foo" $ putStrLn "Here we go!"

runTest : IO ()
runTest 
    = run $ do new (the Int 0) $
               handle {err=String} test pure
                     (\err : String => 
                             putStrLn $ "Error: " ++ err)
