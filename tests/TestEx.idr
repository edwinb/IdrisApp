module TestEx

import Control.App
import Control.App.Console

interface Console e => StateEx e where
  inc : App e Int
  testRes : String -> App e Bool

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

runTest : IO ()
runTest 
    = run $ do new (the Int 0) $
               handle {e=String} test pure
                     (\err : String => 
                             putStrLn $ "Error: " ++ err)
