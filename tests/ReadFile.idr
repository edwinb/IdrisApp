module ReadFile

import Control.App
import Control.App.Console
import Control.App.FileIO

amain : App [Sys] ()
amain = handle (readFile "ReadFile.idr")
               (\str => putStrLn $ "Content:\n" ++ show str)
               (\err : FileEx =>
                       putStrLn $ "FAIL: " ++ show err)

