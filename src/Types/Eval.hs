{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving #-}

module Types.Eval
  where
import Control.Monad.Except
  ( ExceptT(ExceptT)
  , runExceptT
  , mapExceptT
  , MonadError
  , throwError
  , catchError
  )
import Control.Monad.State
  ( StateT
  , evalStateT
  , execStateT
  , mapStateT
  , get
  , put
  , modify'
  , state
  , evalState
  , mapState
  , runState
  , MonadState
  )
import Control.Monad.IO.Class
import Control.Monad.Reader
  ( ReaderT(ReaderT)
  , runReaderT
  , mapReaderT
  , withReaderT
  , reader
  , runReader
  , mapReader
  , withReader
  , MonadReader
  )
import Control.Monad.Writer
  ( writer
  , Writer
  , runWriter
  , censor
  , tell
  )
import Control.Monad.Cont
  ( Cont
  , cont
  , runCont
  , withCont
  )
import Control.Monad.Trans.Class
import Control.Applicative
  ( (<|>)
  , liftA2
  )
import Data.Functor.Identity
import Data.Maybe
  ( isJust
  , mapMaybe
  , catMaybes
  )
import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  

-- Except
type Except = ExceptT E.Error

mapExcept :: (m (Either E.Error a) -> n (Either E.Error b)) -> Except m a -> Except n b
mapExcept = mapExceptT

runExcept :: Monad m => Except m a -> (E.Error -> m a) -> m a
runExcept m catch = runExceptT m >>= either catch return

throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

-- Table
data Table k v m = Table
  { finished :: M.Map k v
  , pending :: M.Map k (v -> Table k v m -> m (Table k v m))
  }

  
emptyTable :: Table v r m
emptyTable = Table { finished = M.empty, pending = M.empty }


concatTable :: (Ord k, Monad m) => Table k v m -> Table k v m -> m (Table k v m)
a `concatTable` b = 
  let
    mb' = M.foldrWithKey (\ k a mb -> mb >>= insertTable k a) (return b) (finished a)
  in 
    M.foldrWithKey (\ k a mb -> mb >>= (lookupTable k `runCont` a)) mb' (pending a)
     
      
lookupTable :: (Ord k, Monad m) => k -> Cont (Table k v m -> m (Table k v m)) v
lookupTable k = cont (\ c n ->
  let
    pending' = M.alter (Just . maybe c (\ f v n -> f v n >>= c v)) k (pending n)
  in
    maybe
      (return (n { pending = pending' }))
      (\ v -> c v n)
      (M.lookup k (finished n)))


insertTable :: (Ord k, Monad m) => k -> v -> Table k v m -> m (Table k v m)
insertTable k v n =
  maybe
    (return (n { finished = finished' }))
    (\ f -> f v (n { finished = finished', pending = pending' }))
    (M.lookup k (pending n))
  where
    finished' = M.insert k v (finished n)
    pending' = M.delete k (pending n)

    
alterTable :: (Ord k, Monad m) => k -> (v -> v) -> Table k v m -> m (Table k v m)
alterTable k f = lookupTable k `runCont` (insertTable k . f)


flushTable :: (Show k, Ord k, Monad m) => v -> k -> Table k v m -> m (Table k v m)
flushTable v k x =
  do{ x' <- insertTable k v x
    ; return (x { finished = M.delete k (finished x') })
    }
    

finaliseTable :: (Show k, Ord k, Monad m) => (k -> v) -> Table k v m -> m (M.Map k v)
finaliseTable flush x =
  do{ x' <- M.foldrWithKey
        (\ k a b ->
           do{ x <- b
             ; let x' = x { pending =  M.delete k (pending x) }
             ; a (flush k) x'
             })
        (return x)
        (pending x)
    ; return (finished x')
    }
    
    
lookupFinalised :: (Show k, Ord k) => v -> k -> M.Map k v -> v
lookupFinalised v k = M.findWithDefault v k


showTable :: (Show k) => Table k v m -> String
showTable x = "finished:"++show (M.keys (finished x))++"\npending:"++show (M.keys (pending x))

instance Show k => Show (Table k v m) where show = showTable


-- Scope
type SelfT m = Table (T.Name Value) (m Value) m
type ClassedT m = SelfT m -> m (SelfT m) 
newtype Bind m a = Bind { appBind :: a -> m a }
type EnvT m = Table T.Ident (Cont (ClassedT m) (m Value)) (Writer (Bind m (SelfT m)))
type ScopeT m = EnvT m -> Writer (Bind m (SelfT m)) (EnvT m)
data ScopeKey = EnvKey T.Ident | SelfKey (T.Name Value)
type Classed = ClassedT Eval
type Scope = ScopeT Eval
type Self = SelfT Eval
type Env = EnvT Eval

instance Monad m => Monoid (Bind m a) where
  mempty = Bind return
  Bind a `mappend` Bind b = Bind (\ s -> a s >>= b)


emptyClassed :: Monad m => ClassedT m
emptyClassed = return


bindClassed :: Monad m => Cont (ClassedT m) (m a) -> Cont (ClassedT m) a
bindClassed = withCont (\ c m x -> do{ a <- m; c a x })


putClassed :: MonadIO m => String -> Cont (ClassedT m) ()
putClassed msg = cont (\ c x -> liftIO (putStrLn ("("++show x++","++msg++")")) >> c () x)


emptyScope :: Monad m => ScopeT m
emptyScope = return

    
putScope :: MonadIO m => String -> Cont (ScopeT m) ()
putScope msg = cont (\ c e ->
  do{ tell (Bind (\ x -> liftIO (putStrLn ("("++show e++","++show x++","++msg++")")) >> return x))
    ; c () e
    })


verboseLookupClassed :: MonadIO m => String -> T.Name Value -> Cont (ClassedT m) (m Value)
verboseLookupClassed label k =
  do{ putClassed (label++"->"++show k)
    ; ev <- lookupTable k
    ; putClassed ("<-"++label++"<-"++show k)
    ; return ev
    }
    
    
verboseLookupScope :: MonadIO m => String -> T.Ident -> Cont (ScopeT m) (Cont (ClassedT m) (m Value))
verboseLookupScope label k =
  do{ putScope (label++"->"++show k)
    ; vr <- lookupTable k
    ; putScope ("<-"++label++"<-"++show k)
    ; return vr
    }

    
verboseInsertClassed :: MonadIO m => String -> T.Name Value -> m Value -> ClassedT m
verboseInsertClassed label k v x =
  do{ liftIO (putStrLn (label++"<-"++show k))
    ; x' <- insertTable k v x
    ; liftIO (putStrLn (show x'))
    ; return x'
    }

    
verboseInsertScope :: String -> T.Ident -> Cont Classed (Eval Value) -> Scope
verboseInsertScope label k v e =
  do{ tell (Bind (\ x -> liftIO (putStrLn (label++"<-"++show k)) >> return x))
    ; e' <- insertTable k (idClassed v) e 
    ; tell (Bind (\ x -> liftIO (putStrLn (show e')) >> return x))
    ; return e'
    }
    
    
verboseAlterClassed :: MonadIO m => String -> T.Name Value -> (m Value -> m Value) -> ClassedT m
verboseAlterClassed label k f = verboseLookupClassed label k `runCont` (verboseInsertClassed label k . f)

      
verboseAlterScope :: String -> T.Ident -> (Cont Classed (Eval Value) -> Cont Classed (Eval Value)) -> Scope
verboseAlterScope label k f = verboseLookupScope label k `runCont` (verboseInsertScope label k . f)
    
-- Eval
-- Id -> IO (Either E.Error a, Id)
newtype Eval a = Eval (Except (Ided IO) a) deriving
  ( Functor
  , Applicative
  , Monad
  , MonadIO
  , MonadError E.Error
  , MonadState Ids
  )
newtype Id = Id { getId :: Integer } deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
type Ided = StateT Ids

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))
    
runIded m = evalStateT m (Id `fmap` iterate (+1) 0)

idClassed :: Cont Classed (Eval a) -> Cont Classed (Eval a)
idClassed = withCont (\ c (Eval a) x ->
    Eval (ExceptT 
      (do{ ea <- runExceptT a
         ; let Eval a' = c (Eval (ExceptT (return ea))) x
         ; runExceptT a'
         })))

runEval :: Eval a -> (E.Error -> IO a) -> IO a
runEval (Eval a) catch = runIded (runExcept a (liftIO . catch)) 

putEval :: Show a => Eval a -> IO ()
putEval m = runEval (m >>= liftIO . putStrLn . show) (putStrLn . show)

runScoped :: Cont Scope (Cont Classed a) -> (a -> Classed) -> (E.Error -> IO ()) -> IO ()
runScoped m c = runEval (n emptyTable >>= finaliseTable throwUnboundVar >> return ())
  where
    (_, Bind n) = runWriter w
    w = 
      do{ e <- (m' `runCont` extract) primitiveBindings
        ; finaliseTable (return . throwUnboundVar) e
        }
    m' =
      do{ ar <- m
        ; return (ar `runCont` c)
        }
    extract n e = do{ tell (Bind n); return e }

  

-- Value
type Node = Classed

emptyNode :: Node
emptyNode = return

data Value = String String | Number Double | Bool Bool | Node Id Node | Symbol Id | BuiltinSymbol BuiltinSymbol
data BuiltinSymbol = SelfSymbol | SuperSymbol | EnvSymbol | ResultSymbol | RhsSymbol | NegSymbol | NotSymbol | AddSymbol | SubSymbol | ProdSymbol | DivSymbol | PowSymbol | AndSymbol | OrSymbol | LtSymbol | GtSymbol | EqSymbol | NeSymbol | LeSymbol | GeSymbol
  deriving (Eq, Ord)
  
instance Show BuiltinSymbol where
  show SelfSymbol = "Self"
  show SuperSymbol = "Super"
  show EnvSymbol = "Env"
  show ResultSymbol = "Result"
  show RhsSymbol = "Rhs"
  show NegSymbol = "Neg"
  show NotSymbol = "Not"
  show AddSymbol = "Add"
  show SubSymbol = "Sub"
  show ProdSymbol = "Prod"
  show DivSymbol = "Div"
  show PowSymbol = "Pow"
  show AndSymbol = "And"
  show OrSymbol = "Or"
  show LtSymbol = "Lt"
  show GtSymbol = "Gt"
  show EqSymbol = "Eq"
  show NeSymbol = "Ne"
  show LeSymbol = "Le"
  show GeSymbol = "Ge"
  
instance Show Value where
  show (String x) = show x
  show (Number x) = show x
  show (Bool x)   = show x
  show (Node i _) = "<Node:" ++ show i ++ ">"
  show (Symbol i) = "<Symbol:" ++ show i ++ ">"
  show (BuiltinSymbol x) = show x

instance Eq Value where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Bool x == Bool x' = x == x'
  Node x _ == Node x' _ = x == x'
  Symbol x == Symbol x' = x == x'
  BuiltinSymbol x == BuiltinSymbol x' = x == x'
  _ == _ = False

instance Ord Value where
  compare (String x)        (String x')        = compare x x'
  compare (String _)        _                  = LT
  compare _                 (String _)         = GT
  compare (Number x)        (Number x')        = compare x x'
  compare (Number _)        _                  = LT
  compare _                 (Number _)         = GT
  compare (Bool x)          (Bool x')          = compare x x'
  compare (Bool _)          _                  = LT
  compare _                 (Bool _)           = GT
  compare (Node x _)        (Node x' _)        = compare x x'
  compare (Node _ _)        _                  = LT
  compare _                 (Node _ _)         = GT
  compare (Symbol x)        (Symbol x')        = compare x x'
  compare (Symbol _)        _                  = LT
  compare _                 (Symbol _)         = GT
  compare (BuiltinSymbol x) (BuiltinSymbol x') = compare x x'
  
  
newNode :: MonadState Ids m => m (Node -> Value)
newNode = useId Node
    
unNode :: Value -> Node
unNode = f
  where
    f (String x) = fromSelf $ primitiveStringSelf x
    f (Number x) = fromSelf $ primitiveNumberSelf x
    f (Bool x) = fromSelf $ primitiveBoolSelf x
    f (Node _ vs) = vs
    f (Symbol _) = fromSelf $ emptyTable
    f (BuiltinSymbol _) = fromSelf $ emptyTable
    
    fromSelf :: Self -> Node
    fromSelf r = (`concatTable` r)

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptyTable

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptyTable

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptyTable

newSymbol :: MonadState Ids m => m Value
newSymbol = useId Symbol

selfSymbol :: Value
selfSymbol = BuiltinSymbol SelfSymbol

superSymbol :: Value
superSymbol = BuiltinSymbol SuperSymbol

envSymbol :: Value
envSymbol = BuiltinSymbol EnvSymbol

resultSymbol :: Value
resultSymbol = BuiltinSymbol ResultSymbol

rhsSymbol :: Value
rhsSymbol = BuiltinSymbol RhsSymbol

unopSymbol :: T.Unop -> Value
unopSymbol (T.Neg) = BuiltinSymbol NegSymbol
unopSymbol (T.Not) = BuiltinSymbol NotSymbol

binopSymbol :: T.Binop -> Value
binopSymbol (T.Add) = BuiltinSymbol AddSymbol
binopSymbol (T.Sub) = BuiltinSymbol SubSymbol
binopSymbol (T.Prod) = BuiltinSymbol ProdSymbol
binopSymbol (T.Div) = BuiltinSymbol DivSymbol
binopSymbol (T.Pow) = BuiltinSymbol PowSymbol
binopSymbol (T.And) = BuiltinSymbol AndSymbol
binopSymbol (T.Or) = BuiltinSymbol OrSymbol
binopSymbol (T.Lt) = BuiltinSymbol LtSymbol
binopSymbol (T.Gt) = BuiltinSymbol GtSymbol
binopSymbol (T.Eq) = BuiltinSymbol EqSymbol
binopSymbol (T.Ne) = BuiltinSymbol NeSymbol
binopSymbol (T.Le) = BuiltinSymbol LeSymbol
binopSymbol (T.Ge) = BuiltinSymbol GeSymbol


undefinedNumberOp :: (MonadError E.Error m, Show s) => s -> m a
undefinedNumberOp s = throwError $ E.PrimitiveOperation "Operation undefined for numbers" (show s)

undefinedBoolOp :: (MonadError E.Error m, Show s) => s -> m a
undefinedBoolOp s = throwError $ E.PrimitiveOperation "Operation undefined for booleans" (show s)

primitiveNumberUnop :: MonadError E.Error m => T.Unop -> Double -> m Value
primitiveNumberUnop (T.Neg) x = return . Number $ negate x
primitiveNumberUnop s       _ = undefinedNumberOp s

primitiveBoolUnop :: MonadError E.Error m => T.Unop -> Bool -> m Value
primitiveBoolUnop (T.Not) x = return . Bool $ not x
primitiveBoolUnop s       _ = undefinedBoolOp s

primitiveNumberBinop :: MonadError E.Error m => T.Binop -> Double -> Double -> m Value
primitiveNumberBinop (T.Add)  x y = return . Number $ x + y
primitiveNumberBinop (T.Sub)  x y = return . Number $ x - y
primitiveNumberBinop (T.Prod) x y = return . Number $ x * y
primitiveNumberBinop (T.Div)  x y = return . Number $ x / y
primitiveNumberBinop (T.Pow)  x y = return . Number $ x ** y
primitiveNumberBinop (T.Lt)   x y = return . Bool $ x < y
primitiveNumberBinop (T.Gt)   x y = return . Bool $ x > y
primitiveNumberBinop (T.Eq)   x y = return . Bool $ x == y
primitiveNumberBinop (T.Ne)   x y = return . Bool $ x /= y
primitiveNumberBinop (T.Le)   x y = return . Bool $ x <= y
primitiveNumberBinop (T.Ge)   x y = return . Bool $ x >= y
primitiveNumberBinop s        _ _ = undefinedNumberOp s

primitiveBoolBinop :: MonadError E.Error m => T.Binop -> Bool -> Bool -> m Value
primitiveBoolBinop (T.And) x y = return . Bool $ x && y
primitiveBoolBinop (T.Or)  x y = return . Bool $ x || y
primitiveBoolBinop (T.Lt)  x y = return . Bool $ x < y
primitiveBoolBinop (T.Gt)  x y = return . Bool $ x > y
primitiveBoolBinop (T.Eq)  x y = return . Bool $ x == y
primitiveBoolBinop (T.Ne)  x y = return . Bool $ x /= y
primitiveBoolBinop (T.Le)  x y = return . Bool $ x <= y
primitiveBoolBinop (T.Ge)  x y = return . Bool $ x >= y
primitiveBoolBinop s       _ _ = undefinedBoolOp s

primitiveBindings :: Table k v m
primitiveBindings = emptyTable

