module TestEx

import Control.App
import Control.App.Console

namespace StateEx

  -- An interface which allows incrementing an internal state, and reading
  -- a string from the console
  public export
  interface Console e => StateEx e where
    -- Increment the state and return the new state
    inc : App e Integer

    -- Prompt for a name and greet the user, returns True if it's endString,
    -- might throw an exception.
    greet : (endString : String) -> App e Bool

  -- We can implement StateEx, as long as we can read from the console, we have
  -- an Integer state available, and we're allowed to throw Strings as
  -- exceptions.  In this case, we throw an exception on reading a magic
  -- word...
  export
  Has [Console, State "i" Integer, Exception String] e => StateEx e where
    inc
        = do count <- get "i"
             put "i" (count + 1)
             pure (count + 1)

    greet endString
        = do count <- get "i"
             inp <- getStr
             case inp of
                  "Xyzzy" => throw "Nothing happens"
                  _ => if inp == endString
                          then pure True
                          else do putStrLn $ "Hello " ++ inp
                                  putStrLn $ "This is greeting number " ++ show count
                                  pure False

-- Use the above interface to keep greeting a user, and print how many
-- greetings there've been
greeter : Has [StateEx] e => App e ()
greeter
    = do putStr "Name: "
         inc
         done <- greet "DONE"
         if done
            then pure ()
            else greeter

runTest : IO ()
runTest 
    = run $ do new 0 $ -- initialise greeting count
               -- We can only run the interface if we handle
               -- the resulting exception:
               handle (do greeter
                          putStrLn "Bye!")
                      pure
                      (\err : String =>
                              putStrLn $ "Error: " ++ err)
