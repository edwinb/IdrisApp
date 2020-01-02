module Control.App

import Data.List
import Data.IORef

public export
data Effect : Type where
     St : Type -> Effect
     Exc : Type -> Effect
     Sys : Effect

public export
data HasEff : Effect -> List Effect -> Type where
     Here : HasEff e (e :: es)
     There : HasEff e es -> HasEff e (e' :: es)

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

public export
data NotException : Effect -> Type where
     StNotE : NotException (St t)
     SysNotE : NotException Sys

public export
data NotState : Effect -> Type where
     ExcNotS : NotState (Exc t)
     SysNotS : NotState Sys

public export
data Linear : List Effect -> Type where
     EmptyLin : Linear []
     RestLin : NotException e => Linear es -> Linear (e :: es)

public export
data Stateless : List Effect -> Type where
     EmptySt : Stateless []
     RestSt : NotState e => Stateless es -> Stateless (e :: es)

export
data Env : List Effect -> Type where
     None : Env []
     Ref : IORef t -> Env es -> Env (St t :: es)
     SkipE : Env es -> Env (Exc t :: es)
     SkipP : Env es -> Env (Sys :: es)

getState : Env es -> (p : HasEff (St t) es) -> IORef t
getState (Ref r env) Here = r
getState (Ref r env) (There p) = getState env p
getState (SkipE env) (There p) = getState env p
getState (SkipP env) (There p) = getState env p

data OneOf : List Type -> Type where
     First : e -> OneOf (e :: es)
     Later : OneOf es -> OneOf (e :: es)

Uninhabited (OneOf []) where
  uninhabited (First x) impossible
  uninhabited (Later x) impossible

public export
0 excTy : List Effect -> List Type
excTy [] = []
excTy (St t :: es) = excTy es
excTy (Exc e :: es) = e :: excTy es
excTy (Sys :: es) = excTy es

0 execTy : List Effect -> Type -> Type
execTy es ty = Either (OneOf (excTy es)) ty

export
data App : List Effect -> Type -> Type where
     MkApp : (1 prog : Env e -> IO (execTy e t)) -> App e t

pureApp : a -> App e a
pureApp x = MkApp (\env => pure (Right x))

bindApp : App e a -> (a -> App e b) -> App e b
bindApp (MkApp prog) k
    = MkApp $ \env =>
          do Right res <- prog env
                   | Left err => pure (Left err)
             let MkApp ka = k res
             ka env

absurdWith : (1 v : a) -> OneOf [] -> any
absurdWith v (First p) impossible

-- Prove that we don't need the error checking case in 'bindL', so that the
-- continuation will definitely be used
noError : (1 k : something) ->
          Linear e -> OneOf (excTy e) -> Env e -> 
          any
noError k EmptyLin p None = absurdWith k p
noError k (RestLin p) (Later q) (SkipE env) = noError k p q env
noError k (RestLin p) q (SkipP env) = noError k p q env
noError k (RestLin p) q (Ref r env) = noError k p q env

export
bindL : Linear e => (1 act : App e a) -> (1 k : a -> App e b) -> App e b
bindL (MkApp prog) k
    = MkApp $ \env =>
          io_bind (prog env) $ \p =>
             case p of
                  Left err => noError k %search err env
                  Right res => 
                         case k res of
                              MkApp iokr => iokr env

export
lift : App e t -> App (eff :: e) t
lift (MkApp p)
    = MkApp (\env => 
          case env of
               Ref r env' => p env'
               SkipP env' => p env'
               SkipE env' => 
                  do res <- p env'
                     case res of
                          Left err => pure (Left (Later err))
                          Right ok => pure (Right ok))

export
Functor (App es) where
  map f ap = bindApp ap $ \ap' => pureApp (f ap')

export
Applicative (App es) where
  pure = pureApp
  (<*>) f a = bindApp f $ \f' =>
              bindApp a $ \a' => pure (f' a')

export
Monad (App es) where
  (>>=) = bindApp

export
new : a -> App (St a :: es) t -> App es t
new val (MkApp prog)
    = MkApp $ \env => 
          do ref <- newIORef val
             prog (Ref ref env)

public export
interface State t es where
  get : App es t
  put : t -> App es ()

export
HasEff (St t) es => State t es where
  get
      = MkApp $ \env =>
            do let ref = getState env %search
               val <- readIORef ref
               pure (Right val)
  put val
      = MkApp $ \env =>
            do let ref = getState env %search
               writeIORef ref val
               pure (Right ())

public export
interface Exception e es where
  throw : e -> App es a
  catch : App es a -> (err : e -> App es a) -> App es a

findException : Env es -> HasEff (Exc e) es -> e -> OneOf (excTy es)
findException (SkipE env) Here err = First err
findException (Ref r env) (There p) err = findException env p err
findException (SkipE env) (There p) err = Later $ findException env p err
findException (SkipP env) (There p) err = findException env p err

findError : Env es -> HasEff (Exc e) es -> OneOf (excTy es) -> Maybe e
findError (SkipE env) Here (First err) = Just err
findError (SkipE env) Here (Later p) = Nothing -- wrong execption
findError (SkipE env) (There p) (First err) = Nothing -- wrong exception
findError (SkipE env) (There p) (Later q) = findError env p q
findError (Ref r env) (There p) err = findError env p err
findError (SkipP env) (There p) err = findError env p err

export
HasEff (Exc e) es => Exception e es where
  throw err
      = MkApp $ \env =>
           pure (Left (findException env %search err))
  catch (MkApp prog) handler
      = MkApp $ \env =>
           do res <- prog env
              case res of
                   Left err =>
                        case findError env %search err of
                             Nothing => pure (Left err)
                             Just err' =>
                                  let MkApp e' = handler err' in
                                      e' env
                   Right ok => pure (Right ok) 

export
handle : App (Exc e :: es) a ->
         (ok : a -> App es b) ->
         (err : e -> App es b) -> App es b
handle (MkApp prog) onok onerr
    = MkApp $ \env =>
          do res <- prog (SkipE env)
             case res of
                  Left (First err) => 
                        let MkApp err' = onerr err in
                            err' env
                  Left (Later p) => 
                        -- different exception, so rethrow
                        pure (Left p)
                  Right ok => 
                        let MkApp ok' = onok ok in
                            ok' env

public export 
interface PrimIO es where
  primIO : IO a -> App es a
  -- Copies the environment, to make sure states are local to threads
  fork : App es () -> App es ()

copyEnv : Env es -> IO (Env es)
copyEnv None = pure None
copyEnv (Ref t env)
    = do val <- readIORef t
         t' <- newIORef val
         env' <- copyEnv env
         pure (Ref t' env')
copyEnv (SkipE env)
    = do env' <- copyEnv env
         pure (SkipE env')
copyEnv (SkipP env)
    = do env' <- copyEnv env
         pure (SkipP env')

clearEnv : Env es -> IO (execTy es ())
clearEnv None = pure (Right ())
clearEnv (Ref t env) = clearEnv env
clearEnv (SkipE env)
    = do e' <- clearEnv env
         case e' of
              Left p => pure $ Left (Later p)
              Right ok => pure $ Right ok
clearEnv (SkipP env) = clearEnv env

export
HasEff Sys es => PrimIO es where
  primIO io 
      = MkApp $ \env =>
            do res <- io
               pure (Right res)
  fork proc
      = MkApp $ \env =>
            do fork (do env' <- copyEnv env
                        let MkApp p' = proc
                        p' env'
                        pure ())
               pure (Right ())


export
run : App [Sys] a -> IO a
run (MkApp prog) 
    = do Right res <- prog (SkipP None)
               | Left err => absurd err
         pure res

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t
