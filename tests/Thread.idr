import Control.App
import Control.App.Console

thread : Has [Console] e => String -> App e ()
thread str
    = do putStrLn str
         thread str

tmain : App Init ()
tmain
    = do fork (thread "Thread")
         thread "Main"
