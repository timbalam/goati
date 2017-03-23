{-# LANGUAGE FlexibleContexts, Rank2Types #-}

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
data Table k v = Table
  { finished :: M.Map k v
  , pending :: M.Map k (v -> Table k v -> Table k v)
  }
  
instance Ord k => Monoid (Table k v) where
  mempty = Table { finished = M.empty, pending = M.empty }
  a `mappend` b = M.foldrWithKey lookupTable b' (pending a)
    where
      b' = M.foldrWithKey insertTable b (finished a)
      
lookupTable :: Ord k => k -> (v -> Table k v -> Table k v) -> Table k v -> Table k v
lookupTable k c n =
  maybe
    (n { pending = pending' })
    (\ v -> c v n)
    (M.lookup k (finished n))
  where
    pending' = M.alter (Just . maybe c (\ f v -> c v . f v)) k (pending n)


insertTable :: Ord k => k -> v -> Table k v -> Table k v
insertTable k v n =
  maybe
    n'
    (\ f -> f v n')
    (M.lookup k (pending n))
  where
    finished' = M.insert k v (finished n)
    pending' = M.delete k (pending n)
    n' = n { finished = finished', pending = pending' }

    
alterTable :: Ord k => k -> (v -> v) -> Table k v -> Table k v
alterTable k f = lookupTable k (insertTable k . f)

-- Scope
data Scope v = Scope
  { env :: Table T.Ident v
  , self :: Table (T.Name Value) v
  }
data ScopeKey = EnvKey T.Ident | SelfKey (T.Name Value)

instance Monoid (Scope v) where
  mempty = Scope { env = mempty, self = mempty }
  a `mappend` b = Scope { env = env a `mappend` env b, self = self a `mappend` self b }


lookupScopeWith :: Ord k => k -> (Scope v -> Table k v) -> ((Table k v -> Table k v) -> Scope v -> Scope v) -> (v -> Scope v -> Scope v) -> Scope v -> Scope v
lookupScopeWith k get set c s =  set (lookupTable k c') s
  where
    c' v n = let s' = c v (set (const n) s) in get s'

lookupScope :: ScopeKey -> (v -> Scope v -> Scope v) -> Scope v -> Scope v
lookupScope (EnvKey x) = lookupScopeWith x env (\ f s -> s { env = f (env s) })
lookupScope (SelfKey v) = lookupScopeWith v self (\ f s -> s { self = f (self s) })

insertScopeWith :: Ord k => k -> v -> ((Table k v -> Table k v) -> Scope v -> Scope v) -> Scope v -> Scope v
insertScopeWith k v set s =  set (insertTable k v) s

insertScope :: ScopeKey -> v -> Scope v -> Scope v
insertScope (EnvKey x) v = insertScopeWith x v (\ f s -> s { env = f (env s) })
insertScope k@(SelfKey y) v
    | T.Ref x <- y = lookupScope k (insertScope (EnvKey x)) . insertSelf
    | T.Key _ <- y = insertSelf
  where
    insertSelf = insertScopeWith y v (\ f s -> s { self = f (self s) })
    
    
alterScope :: ScopeKey -> (v -> v) -> Scope v -> Scope v
alterScope k f = lookupScope k (insertScope k . f)
  
    
-- Eval
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
type Node = Scope Value
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
    f (Symbol _) = fromSelf $ mempty
    f (BuiltinSymbol _) = fromSelf $ mempty
    
    fromSelf :: Self -> Node
    fromSelf r = mempty

type Self = Table (T.Name Value) ()
primitiveStringSelf :: String -> Self
primitiveStringSelf x = mempty

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = mempty

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = mempty

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

primitiveBindings :: Ord k => Table k v
primitiveBindings = mempty

