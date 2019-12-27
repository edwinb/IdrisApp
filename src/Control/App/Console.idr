module Control.App.Console

import Control.App

public export
interface Console e where
  putStr : String -> App e ()
  getStr : App e String

export 
PrimIO e => Console e where
  putStr str = primIO $ putStr str
  getStr = primIO $ getLine

putStrLn : Console e => String -> App e ()
putStrLn str = putStr (str ++ "\n")
