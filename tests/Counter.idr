module Main

import Control.App
import Control.App.Console

data Counter : Type where

using (Has [Console, State Counter Integer] e)
  count : Nat -> Integer -> App e ()
  count Z x
      = pure ()
  count (S k) x
      = do val <- get Counter
           put Counter (val + x)
           putStr (show val ++ "\n")
           count k x

cmain : App Init ()
cmain
    = do new 0 $
         count 10000 2

main : IO ()
main = run cmain
