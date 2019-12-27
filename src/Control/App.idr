module Control.App

import Data.List
import Data.IORef

public export
data Effect : Type where
     St : Type -> Effect
     Exc : Type -> Effect
     PIO : Effect

public export
data HasEff : Effect -> List Effect -> Type where
     Here : HasEff e (e :: es)
     There : HasEff e es -> HasEff e (e' :: es)

export
data Env : List Effect -> Type where
     None : Env []
     Ref : IORef t -> Env es -> Env (St t :: es)
     SkipE : Env es -> Env (Exc t :: es)
     SkipP : Env es -> Env (PIO :: es)

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
execTy (PIO :: es) ty = execTy es ty

public export
data Execution = Linear | NonLinear

export
data AppE : Execution -> List Effect -> Type -> Type where
     Pure : (x : a) -> AppE l es a
     Bind : AppE l es a -> (a -> AppE l es b) -> AppE l es b
     BindL : (1 act : AppE Linear es a) -> 
             (1 k : a -> AppE Linear es b) -> AppE Linear es b

     New : a -> AppE l (St a :: es) t -> AppE l es t
     Get : HasEff (St t) es => AppE l es t
     Put : HasEff (St t) es => t -> AppE l es ()

     Throw : HasEff (Exc e) es => e -> AppE NonLinear es a
     Catch : HasEff (Exc e) es => 
             AppE l' es a -> 
             (err : e -> AppE l es a) -> AppE l es a
     Handle : AppE NonLinear (Exc e :: es) a ->
              (ok : a -> AppE l es b) ->
              (err : e -> AppE l es b) -> AppE l es b
     
     Prim : HasEff PIO es => PrimIO a -> AppE l es a

export
Functor (AppE l es) where
  map f ap = Bind ap $ \ap' => Pure (f ap')

export
Applicative (AppE l es) where
  pure = Pure
  (<*>) f a = Bind f $ \f' =>
              Bind a $ \a' => pure (f' a')

export
Monad (AppE l es) where
  (>>=) = Bind

namespace LinearBind
  export
  (>>=) : (1 act : AppE Linear e a) ->
          (1 k : a -> AppE Linear e b) -> AppE Linear e b
  (>>=) = BindL

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

exec : Env es -> AppE l es t -> (t -> IO (execTy es a)) -> IO (execTy es a)
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

exec env (Prim io) k 
    = do op <- primIO io
         k op

export
new : a -> AppE l (St a :: es) t -> AppE l es t
new = New

public export
interface State t es where
  get : AppE l es t
  put : t -> AppE l es ()

export
HasEff (St t) es => State t es where
  get = Get
  put = Put

export
handle : AppE NonLinear (Exc e :: es) a ->
         (ok : a -> AppE l es b) ->
         (err : e -> AppE l es b) -> AppE l es b
handle = Handle

public export
interface Exception e es where
  throw : e -> AppE NonLinear es a
  catch : AppE l' es a -> (err : e -> AppE l es a) -> AppE l es a

export
HasEff (Exc e) es => Exception e es where
  throw = Throw
  catch = Catch

public export 
interface PrimIO es where
  primIO : IO a -> AppE l es a

export
HasEff PIO es => PrimIO es where
  primIO = Prim . toPrim

export
run : AppE Linear [PIO] a -> IO a
run prog = exec (SkipP None) prog pure

public export
0 Has : List (a -> Type) -> a -> Type
Has [] es = ()
Has [e] es = e es
Has (e :: es') es = (e es, Has es' es)

public export
App : List Effect -> Type -> Type
App e a = forall l . AppE l e a

public export
AppL : List Effect -> Type -> Type
AppL = AppE Linear

infix 5 @@

public export
data Res : (a : Type) -> (a -> Type) -> Type where
     (@@) : (val : a) -> (1 r : t val) -> Res a t

