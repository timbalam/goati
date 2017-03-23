{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving #-}

module Types.Eval
  where
import Control.Monad.Except
  ( ExceptT
  , runExceptT
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
  )
import Control.Monad.Trans.Class
import Control.Applicative
  ( (<|>)
  , liftA2
  )
import Control.Monad( join )
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
    M.foldrWithKey (\ k a mb -> mb >>= lookupTable k a) mb' (pending a)
     
      
lookupTable :: (Ord k, Monad m) => k -> (v -> Table k v m -> m (Table k v m)) -> Table k v m -> m (Table k v m)
lookupTable k c n =
  maybe
    (return (n { pending = pending' }))
    (\ v -> c v n)
    (M.lookup k (finished n))
  where
    pending' = M.alter (Just . maybe c (\ f v n -> f v n >>= c v)) k (pending n)


insertTable :: (Ord k, Monad m) => k -> v -> Table k v m -> m (Table k v m)
insertTable k v n =
  maybe
    (return n')
    (\ f -> f v n')
    (M.lookup k (pending n))
  where
    finished' = M.insert k v (finished n)
    pending' = M.delete k (pending n)
    n' = n { finished = finished', pending = pending' }

    
alterTable :: (Ord k, Monad m) => k -> (v -> v) -> Table k v m -> m (Table k v m)
alterTable k f = lookupTable k (insertTable k . f)


-- Scope
type SelfT m = Table (T.Name Value) (Eval Value) m
type ClassedT m = SelfT m -> m (SelfT m) 
newtype Bind m a = Bind { appBind :: a -> m a }
type EnvT m = Table T.Ident ((Eval Value -> ClassedT m) -> ClassedT m) (Writer (Bind m (SelfT m)))
type ScopeT m = EnvT m -> Writer (Bind m (SelfT m)) (EnvT m)
type Self = SelfT Identity
type Classed = ClassedT Identity
type Env = EnvT Identity
data ScopeKey = EnvKey T.Ident | SelfKey (T.Name Value)

instance Monad m => Monoid (Bind m a) where
  mempty = Bind return
  Bind a `mappend` Bind b = Bind (\ s -> a s >>= b)



lookupScope :: Monad m => ScopeKey -> (((Eval Value -> ClassedT m) -> ClassedT m) -> ScopeT m) -> ScopeT m
lookupScope (EnvKey x) c = lookupTable x c
-- lookupTable k :: (Eval Value -> Classed m) -> Classed m
lookupScope (SelfKey k) c = c (lookupTable k)


insertScope :: Monad m => ScopeKey -> ((Eval Value -> ClassedT m) -> ClassedT m) -> ScopeT m
-- insertTable k :: ((Eval Value -> ClassedT m) -> ClassedT m) -> EnvT m -> Writer (EnvT m, ClassedT m)
insertScope (EnvKey x) mv env = insertTable x mv env
-- insertTable k :: Eval Value -> Classed m
insertScope (SelfKey k) mv env =
  do{ tell (Bind (mv (insertTable k)))
    ; case k of
        T.Ref x -> lookupScope (SelfKey k) (insertScope (EnvKey x)) env
        T.Key _ -> return env
    }
      
      
alterScope :: Monad m => ScopeKey -> (((Eval Value -> ClassedT m) -> ClassedT m) -> ((Eval Value -> ClassedT m) -> ClassedT m)) -> ScopeT m
alterScope k f = lookupScope k (insertScope k . f)
  
    
-- Eval
newtype Eval a = Eval (Except (Ided IO) a) deriving
  ( Functor
  , Applicative
  , Monad
  , MonadIO
  , MonadError E.Error
  , MonadState Id
  )
newtype Id = Id { getId :: Integer } deriving (Eq, Ord, Show)
type Ided = StateT Id

useId :: MonadState Id m => (Id -> a) -> m a
useId ctr =
  do{ i <- get
    ; modify' (Id . (+1) . getId)
    ; return (ctr i)
    }
    
runIded m = evalStateT m (Id 0)

-- Value
type Node = Self
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
  
  
newNode :: MonadState Id m => m (Node -> Value)
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
    fromSelf r = r

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptyTable

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptyTable

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptyTable

newSymbol :: MonadState Id m => m Value
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

