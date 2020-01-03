module ReadFile

import Control.App
import Control.App.Console
import Control.App.FileIO

amain : App Init ()
amain = withFileIO
            (readFile "ReadFile.idr")
            (\str => putStrLn $ "Content:\n" ++ show str)
            (\err => putStrLn $ "FAIL: " ++ show err)

