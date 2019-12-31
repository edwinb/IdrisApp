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

public export
0 execTy : List Effect -> Type -> Type
execTy [] ty = ty
execTy (St t :: es) ty = execTy es ty
execTy (Exc e :: es) ty = Either e (execTy es ty)
execTy (Sys :: es) ty = execTy es ty

export
data App : List Effect -> Type -> Type where
     Pure : (x : a) -> App es a
     Bind : App es a -> (a -> App es b) -> App es b
     BindL : Linear es =>
             (1 act : App es a) -> 
             (1 k : a -> App es b) -> App es b

     New : a -> App (St a :: es) t -> App es t
     Get : HasEff (St t) es => App es t
     Put : HasEff (St t) es => t -> App es ()

     Throw : HasEff (Exc e) es => e -> App es a
     Catch : HasEff (Exc e) es => 
             App es a -> 
             (err : e -> App es a) -> App es a
     Handle : App (Exc e :: es) a ->
              (ok : a -> App es b) ->
              (err : e -> App es b) -> App es b

     Fork : HasEff Sys es => App es () -> App es ()
     Prim : HasEff Sys es => PrimIO a -> App es a

export
Functor (App es) where
  map f ap = Bind ap $ \ap' => Pure (f ap')

export
Applicative (App es) where
  pure = Pure
  (<*>) f a = Bind f $ \f' =>
              Bind a $ \a' => pure (f' a')

export
Monad (App es) where
  (>>=) = Bind

throwIn : Env es -> HasEff (Exc e) es -> e -> 
          IO (execTy (es ++ rest) a)
throwIn (SkipE es) Here e = pure (Left e)
throwIn (Ref r es) (There p) e = throwIn es p e
throwIn (SkipE es) (There p) e 
    = do res <- throwIn es p e
         pure (Right res)
throwIn (SkipP es) (There p) e = throwIn es p e

findRes : Env es -> HasEff (Exc e) es -> execTy es a -> Maybe e
findRes (SkipE env) (There p) (Left _) = Nothing -- wrong exception
findRes (SkipE env) (There p) (Right r) = findRes env p r
findRes (Ref r env) (There p) t = findRes env p t
findRes (SkipP env) (There p) t = findRes env p t
findRes None _ _ = Nothing
findRes _ Here (Left ex) = Just ex
findRes _ Here _ = Nothing

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
clearEnv None = pure ()
clearEnv (Ref t env) = clearEnv env
clearEnv (SkipE env)
    = do e' <- clearEnv env
         pure (Right e')
clearEnv (SkipP env) = clearEnv env

exec : Env es -> App es t -> (t -> IO (execTy es a)) -> IO (execTy es a)
exec env (Pure val) k = k val
exec env (Bind act next) k 
    = exec env act (\res => exec env (next res) k)
exec env (BindL act next) k 
    = exec env act (\res => exec env (next res) k)
exec env (New val prog) k
    = do r <- newIORef val
         exec (Ref r env) prog k
exec env (Get @{p}) k
    = do let ref = getState env p
         val <- readIORef ref
         k val
exec env (Put @{p} val) k
    = do let ref = getState env p
         writeIORef ref val
         k ()
exec env (Throw @{p} e) k 
    = rewrite sym (appendNilRightNeutral es) in 
        throwIn env p e {rest = []}
exec env (Handle prog ok err) k
    = do res <- exec (SkipE env) prog 
                     (\res => do res' <- exec env (ok res) k
                                 pure (Right res'))
         case res of
              Left ex => exec env (err ex) k
              Right ok => pure ok
exec env (Catch @{p} prog err) k
    = do res <- exec env prog k
         case findRes env p res of
              Just ex => exec env (err ex) k
              Nothing => pure res
exec env (Fork proc) k
    = do fork (do env' <- copyEnv env
                  exec env proc (\u => clearEnv env)
                  pure ())
         k ()
exec env (Prim io) k 
    = do op <- primIO io
         k op

export
bindL : Linear e =>
        (1 act : App e a) ->
        (1 k : a -> App e b) -> App e b
bindL = BindL

export
new : a -> App (St a :: es) t -> App es t
new = New

public export
interface State t es where
  get : App es t
  put : t -> App es ()

export
HasEff (St t) es => State t es where
  get = Get
  put = Put

export
handle : App (Exc e :: es) a ->
         (ok : a -> App es b) ->
         (err : e -> App es b) -> App es b
handle = Handle

public export
interface Exception e es where
  throw : e -> App es a
  catch : App es a -> (err : e -> App es a) -> App es a

export
HasEff (Exc e) es => Exception e es where
  throw = Throw
  catch = Catch

-- Define some useful generic exceptions here?
-- OS, IO, etc? 'SomeException'
-- IOException, define a few POSIX services - files, directories, etc...

public export 
interface PrimIO es where
  primIO : IO a -> App es a
  -- Copies the environment, to make sure states are local to threads
  fork : App es () -> App es ()

export
HasEff Sys es => PrimIO es where
  primIO = Prim . toPrim
  fork = Fork

export
run : App [Sys] a -> IO a
run prog = exec (SkipP None) prog pure

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t
