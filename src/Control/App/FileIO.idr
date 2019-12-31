module Control.App.FileIO

import Control.App

import Data.List
import Data.Strings
import System.File

public export
data FileEx = GenericFileEx Int -- errno
            | FileReadError
            | FileWriteError
            | FileNotFound
            | PermissionDenied
            | FileExists

export
Show FileEx where
  show (GenericFileEx errno) = "File error: " ++ show errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

toFileEx : FileError -> FileEx
toFileEx (GenericFileError i) = GenericFileEx i
toFileEx FileReadError = FileReadError
toFileEx FileWriteError = FileWriteError
toFileEx FileNotFound = FileNotFound
toFileEx PermissionDenied = PermissionDenied
toFileEx FileExists = FileExists

public export
interface Has [Exception FileEx] e => FileIO e where
  withFile : String -> Mode -> 
             (onError : FileEx -> App e a) ->
             (onOpen : File -> App e a) -> 
             App e a
  fGetStr : File -> App e String
  fPutStr : File -> String -> App e ()
  fEOF : File -> App e Bool

-- TODO : Add Binary File IO with buffers

export
readFile : FileIO e => String -> App e String
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

export
Has [PrimIO, Exception FileEx] e => FileIO e where
  withFile fname m onError proc
      = do Right h <- primIO $ openFile fname m
              | Left err => onError (toFileEx err)
           res <- catch (proc h) onError
           pure res

  fGetStr f
      = do Right str <- primIO $ fGetLine f
              | Left err => throw (toFileEx err)
           pure str

  fPutStr f str
      = do Right () <- primIO $ File.fPutStr f str
               | Left err => throw (toFileEx err)
           pure ()

  fEOF f = primIO $ fEOF f

export
withFileIO : Has [PrimIO] e =>
             App (Exc FileEx :: e) a ->
             (ok : a -> App e b) ->
             (err : FileEx -> App e b) -> App e b
withFileIO prog ok err = handle prog ok err
