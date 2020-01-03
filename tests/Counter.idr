module Main

import Control.App
import Control.App.Console

count : Has [Console, State Integer] e =>
        Nat -> Integer -> App e ()
count Z x
    = pure ()
count (S k) x
    = do val <- get
         put (val + x)
         putStr (show val ++ "\n")
         count k x

cmain : App Init ()
cmain
    = do new 0 $
         count 10000 2

main : IO ()
main = run cmain
