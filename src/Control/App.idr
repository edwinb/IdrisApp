module Control.App

import Data.IORef

public export
Error : Type
Error = Type

public export
data HasErr : Error -> List Error -> Type where
     Here : HasErr e (e :: es)
     There : HasErr e es -> HasErr e (e' :: es)

public export
data Path : Type where
     [noHints]
     MayThrow : Path
     NoThrow : Path

%hint public export
dpath : Path
dpath = MayThrow

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

public export
0 excTy : List Error -> List Type
excTy [] = []
excTy (e :: es) = e :: excTy es

data OneOf : List Type -> Path -> Type where
     First : e -> OneOf (e :: es) MayThrow
     Later : OneOf es MayThrow -> OneOf (e :: es) MayThrow

updateP : OneOf es p -> OneOf es p'
updateP {p=MayThrow} {p'=MayThrow} x = x

Uninhabited (OneOf [] p) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

Uninhabited (OneOf es NoThrow) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

0 execTy : Path -> List Error -> Type -> Type
execTy p es ty = Either (OneOf (excTy es) p) ty

export
data App : (l : Path) => (es : List Error) -> Type -> Type where
     MkApp : (1 prog : IO (execTy l e t)) -> App {l} e t

public export
data SafeBind : Path -> (l' : Path) -> Type where
     [search l']
     SafeSame : SafeBind l l
     SafeToThrow : SafeBind NoThrow MayThrow

bindApp : SafeBind l l' =>
          App {l} e a -> (a -> App {l=l'} e b) -> App {l=l'} e b
bindApp (MkApp prog) next
    = MkApp $
         do Right res <- prog
                | Left err => pure (Left (updateP err))
            let MkApp r = next res
            r

absurdWith : (1 x : a) -> OneOf e NoThrow -> any
absurdWith x (First p) impossible

export
bindL : App {l=NoThrow} e a -> (1 k : a -> App {l} e b) -> App {l} e b
bindL (MkApp prog) k
    = MkApp $
         io_bind prog $ \r =>
              case r of
                   Left err => absurdWith k err
                   Right res =>
                         let MkApp ka = k res in ka

pureApp : a -> App {l} e a
pureApp x = MkApp $ pure (Right x)

export
Functor (App {l} es) where
  map f ap = bindApp ap $ \ap' => pureApp (f ap')

export
Applicative (App {l} es) where
  pure = pureApp
  (<*>) f a = bindApp f $ \f' =>
              bindApp a $ \a' => pure (f' a')

export
Monad (App es) where
  (>>=) = bindApp -- won't get used, but handy to have the instance

export
(>>=) : SafeBind l l' =>
        App {l} e a -> (k : a -> App {l=l'} e b) -> App {l=l'} e b
(>>=) = bindApp

export
data State : Type -> List Error -> Type where
     MkState : IORef t -> State t e

%hint export
mapState : State t e -> State t (eff :: e)
mapState (MkState s) = MkState s

export
get : State t e => App {l} e t
get @{MkState r}
    = MkApp $
          do val <- readIORef r
             pure (Right val)

export
put : State t e => t -> App {l} e ()
put @{MkState r} val
    = MkApp $
          do writeIORef r val
             pure (Right ())

export
new : t -> (State t e => App {l} e a) -> App {l} e a
new val prog
    = MkApp $
         do ref <- newIORef val
            let st = MkState ref
            let MkApp res = prog @{st}
            res

public export
interface Exception err e where
  throw : err -> App e a
  catch : App e a -> (err -> App e a) -> App e a

findException : HasErr e es -> e -> OneOf (excTy es) MayThrow
findException Here err = First err
findException (There p) err = Later $ findException p err

findError : HasErr e es -> OneOf (excTy es) MayThrow -> Maybe e
findError Here (First err) = Just err
findError (There p) (Later q) = findError p q
findError _ _ = Nothing

export
HasErr e es => Exception e es where
  throw err = MkApp $ pure (Left (findException %search err))
  catch (MkApp prog) handler
      = MkApp $
           do res <- prog
              case res of
                   Left err =>
                        case findError %search err of
                             Nothing => pure (Left err)
                             Just err' =>
                                  let MkApp e' = handler err' in
                                      e'
                   Right ok => pure (Right ok) 

export
handle : App (err :: e) a ->
         (onok : a -> App e b) ->
         (onerr : err -> App e b) -> App e b
handle (MkApp prog) onok onerr
    = MkApp $
          do res <- prog
             case res of
                  Left (First err) => 
                        let MkApp err' = onerr err in
                            err'
                  Left (Later p) => 
                        -- different exception, so rethrow
                        pure (Left p)
                  Right ok => 
                        let MkApp ok' = onok ok in
                            ok'

public export
Init : List Error
Init = [Void]

public export
interface PrimIO e where
  primIO : IO a -> App {l} e a
  -- fork starts a new environment, so that any existing state can't get
  -- passed to it (since it'll be tagged with the wrong environment)
  fork : (forall e' . PrimIO e' => App {l} e' ()) -> App e ()

export
HasErr Void e => PrimIO e where
  primIO op = MkApp $ map Right op
  fork thread
      = MkApp $
            do PrimIO.fork (do let MkApp res = thread {e'=Init}
                               res
                               pure ())
               pure (Right ())

export
run : App Init a -> IO a
run (MkApp prog) 
    = do Right res <- prog
               | Left (First err) => absurd err
         pure res

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t
