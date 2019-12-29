module Control.App.FileIO

import Control.App
import public System.File

public export
interface Exception FileError e => FileIO e where
  withFile : String -> Mode -> 
             (onError : FileError -> App e a) ->
             (onOpen : File -> App e a) -> 
             App e a
  fGetStr : File -> App e String
  fPutStr : File -> String -> App e ()
  fEOF : File -> App e Bool

-- TODO : Add Binary File IO with buffers

export
Has [PrimIO, Exception FileError] e => FileIO e where
  withFile fname m onError proc
      = do Right h <- primIO $ openFile fname m
              | Left err => onError err
           res <- catch (proc h) onError
           pure res

  fGetStr f
      = do Right str <- primIO $ fGetLine f
              | Left err => throw err
           pure str

  fPutStr f str
      = do Right () <- primIO $ File.fPutStr f str
               | Left err => throw err
           pure ()

  fEOF f = primIO $ fEOF f