module Control.App.Console

import Control.App

public export
interface Console e where
  putStr : String -> AppL e ()
  getStr : AppL e String

export 
PrimIO e => Console e where
  putStr str = primIO $ putStr str
  getStr = primIO $ getLine

export
putStrLn : Console e => String -> AppL e ()
putStrLn str = putStr (str ++ "\n")
