module ReadFile

import Control.App
import Control.App.Console
import Control.App.FileIO

import Data.List
import Data.Strings

readFile : FileIO e =>
           String -> App e String
readFile f
    = withFile f Read throw $ \h =>
        do content <- read [] h
           pure (fastAppend content)
  where
    read : List String -> File -> App e (List String)
    read acc h
        = do eof <- fEOF h
             if eof
                then pure (reverse acc)
                else do str <- fGetStr h
                        read (str :: acc) h

amain : App [Sys] ()
amain = handle (readFile "ReadFile.idr")
               (\str => putStrLn $ "Content:\n" ++ show str)
               (\err : FileError => 
                       putStrLn $ "FAIL: " ++ show err)


