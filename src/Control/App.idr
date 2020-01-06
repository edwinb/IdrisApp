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

data AppRes : Type -> Type where
     MkAppRes : (result : a) -> (1 x : %World) -> AppRes a

data App1Res : Type -> Type where
     MkApp1Res : (1 result : a) -> (1 x : %World) -> App1Res a

PrimApp : Type -> Type
PrimApp a = (1 x : %World) -> AppRes a

export
prim_app_pure : a -> PrimApp a
prim_app_pure x = \w => MkAppRes x w

export
prim_app_bind : (1 act : PrimApp a) -> (1 k : a -> PrimApp b) -> PrimApp b
prim_app_bind fn k w
    = let MkAppRes x' w' = fn w in k x' w'

toPrimApp : IO a -> PrimApp a
toPrimApp x 
    = \w => case toPrim x w of
                 MkIORes r w => MkAppRes r w

PrimApp1 : Type -> Type
PrimApp1 a = (1 x : %World) -> App1Res a

export
prim_app1_pure : (1 x : a) -> PrimApp1 a
prim_app1_pure x = \w => MkApp1Res x w

export
prim_app1_bind : (1 act : PrimApp1 a) -> 
                 (1 k : (1 x : a) -> PrimApp1 b) -> PrimApp1 b
prim_app1_bind fn k w
    = let MkApp1Res x' w' = fn w in k x' w'

toPrimApp1 : IO a -> PrimApp1 a
toPrimApp1 x 
    = \w => case toPrim x w of
                 MkIORes r w => MkApp1Res r w

export
data App : (l : Path) => (es : List Error) -> Type -> Type where
     MkApp : (1 prog : (1 w : %World) -> AppRes (execTy l e t)) -> App {l} e t

public export
data SafeBind : Path -> (l' : Path) -> Type where
     [search l']
     SafeSame : SafeBind l l
     SafeToThrow : SafeBind NoThrow MayThrow

bindApp : SafeBind l l' =>
          App {l} e a -> (a -> App {l=l'} e b) -> App {l=l'} e b
bindApp (MkApp prog) next
    = MkApp $ \world =>
          let MkAppRes x' world' = prog world in
              case x' of
                   Right res =>
                         let MkApp r = next res in
                             r world'
                   Left err => MkAppRes (Left (updateP err)) world'

absurdWith : (1 x : a) -> (1 w : b) -> OneOf e NoThrow -> any
absurdWith x w (First p) impossible

export
bindL : App {l=NoThrow} e a -> (1 k : a -> App {l} e b) -> App {l} e b
bindL (MkApp prog) next
    = MkApp $ \world =>
          let MkAppRes x' world' = prog world in
              case x' of
                   Right res =>
                         let MkApp r = next res in
                             r world'
                   Left err => absurdWith next world' err
pureApp : a -> App {l} e a
pureApp x = MkApp $ \w => MkAppRes (Right x) w

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
          prim_app_bind (toPrimApp $ readIORef r) $ \val =>
          MkAppRes (Right val)

export
put : State t e => t -> App {l} e ()
put @{MkState r} val
    = MkApp $
          prim_app_bind (toPrimApp $ writeIORef r val) $ \val =>
          MkAppRes (Right ())

export
new : t -> (State t e => App {l} e a) -> App {l} e a
new val prog
    = MkApp $
         prim_app_bind (toPrimApp $ newIORef val) $ \ref =>
            let st = MkState ref
                MkApp res = prog @{st} in
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
  throw err = MkApp $ MkAppRes (Left (findException %search err))
  catch (MkApp prog) handler
      = MkApp $
           prim_app_bind prog $ \res =>
              case res of
                   Left err =>
                        case findError %search err of
                             Nothing => MkAppRes (Left err)
                             Just err' =>
                                  let MkApp e' = handler err' in
                                      e'
                   Right ok => MkAppRes (Right ok)

export
handle : App (err :: e) a ->
         (onok : a -> App e b) ->
         (onerr : err -> App e b) -> App e b
handle (MkApp prog) onok onerr
    = MkApp $
           prim_app_bind prog $ \res =>
             case res of
                  Left (First err) => 
                        let MkApp err' = onerr err in
                            err'
                  Left (Later p) => 
                        -- different exception, so rethrow
                        MkAppRes (Left p)
                  Right ok => 
                        let MkApp ok' = onok ok in
                            ok'

export
lift : App e a -> App (err :: e) a
lift (MkApp prog)
    = MkApp $
           prim_app_bind prog $ \res =>
            case res of
                 Left err => MkAppRes (Left (Later err))
                 Right ok => MkAppRes (Right ok)

public export
Init : List Error
Init = [Void]

export
run : App {l} Init a -> IO a
run (MkApp prog)
    = primIO $ \w =>
           case (prim_app_bind prog $ \r =>
                   case r of
                        Right res => MkAppRes res
                        Left (First err) => absurd err) w of
                MkAppRes r w => MkIORes r w

public export
interface PrimIO e where
  primIO : IO a -> App {l} e a
  -- fork starts a new environment, so that any existing state can't get
  -- passed to it (since it'll be tagged with the wrong environment)
  fork : (forall e' . PrimIO e' => App {l} e' ()) -> App e ()

export
HasErr Void e => PrimIO e where
  primIO op = MkApp $ \w => let MkAppRes r w = toPrimApp op w in
                                MkAppRes (Right r) w
  fork thread
      = MkApp $
            prim_app_bind
                (toPrimApp $ PrimIO.fork $
                      do run thread
                         pure ())
                    $ \_ =>
               MkAppRes (Right ())

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t
