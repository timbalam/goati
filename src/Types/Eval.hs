{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving, DeriveTraversable #-}

module Types.Eval
  where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding (Endo(Endo), appEndo)
import Control.Monad.Cont
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
import Data.Monoid( Alt(Alt), getAlt )
import Data.Semigroup ( Max(Max) )
import Data.List ( NonEmpty(NonEmpty), head, tail )
--import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Map.Merge as M
--import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  

-- Error
throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError (E.UnboundVar "Unbound var" (show k))

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

throwMultipleDefinitions :: (Show k, MonadError E.Error m) => k -> m a
throwMultipleDefinitions k = throwError (E.MultipleDefinitions "Multiple definitions for var" (show k))


-- Tables
newtype Deferred m a = Deferred (WriterT (Max Word) m a) deriving (Functor, Applicative, Foldable, Traversable, Monad, MonadTrans, MonadError e, MonadIO)

undefer :: Monad m => Deferred m a -> m a
undefer (Deferred w) = do{ (a, _) <- runWriterT w; return a }

deferred :: Monad m => (a, Max Word) -> Deferred m a
deferred = Deferred . writer

newtype Table k v = Table (M.Map k v)
newtype Tables k v = Tables [Table k v]

emptyTable :: Table k v
emptyTable = Table M.empty

lookupTable :: Ord k => k -> Table k v -> Maybe v
lookupTable k (Table x) = M.lookup k x

insertTable :: Ord k => (k, MonadError E.Error m) -> (m v) -> Table k (m v) -> m (Table k v)
insertTable k v (Table x) = Table (M.alterF (maybe (Just v) (throwMultipleDefinitions k)) x)

alterTable :: (Show k, Ord k, MonadError E.Error m) => k -> (m v -> m v) -> Table k (m v) -> Table k (m v)
alterTable k f (Table x) = Table (M.alter (Just . f . maybe (throwUnboundVar k) id) k x)

deleteTable :: Ord k => k -> Table k v -> Table k v
deleteTable k (Table x) = Table (M.delete k x)


showTable :: Show k => Table k v -> String
showTable (Table x) = show (M.keys x)

instance Show k => Show (Table k v) where show = showTable

emptyTables :: Tables k v
emptyTables = Tables []

lookupTables :: (Ord k, Monad m) => k -> Tables k (Deferred m v) -> Maybe (Deferred m v)
-- M.lookup :: k -> Map k v -> Maybe v
lookupTables k (Tables xs) = getAlt (foldMap f (zip (iterate succ mempty) xs))
  where
    f (i, x) = Alt (do{ Deferred w <- lookupTable k x; return (Deferred (tell i >> w)) })

insertTables :: (Ord k, Monad m) => Deferred m k -> Deferred m v -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
-- M.insert :: k -> v -> Map k v -> Map k v
insertTables (Deferred w) v (Tables xs) =
  do{ (k, i) <- runWriterT w
    ; let
        go i [] = go i [emptyTable]
        go i xs@(z:zs)
          | i==minBound = insertTable k v <$> xs
          | otherwise = z:(go (pred i) zs)
    ; return (Tables (go i xs))
    }
      
alterTables :: (Show k, Ord k, Monad m, MonadError E.Error m) => Deferred m k -> (Deferred m v -> Deferred m v) -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
alterTables (Deferred w) f t =
  do{ (k, i) <- runWriterT w
    ; let mv' = f (maybe (throwUnboundVar k) id (takeTables k t)) 
    ; insertTables (Deferred (writer (k, i))) mv' t
    }
  where 
    takeTables :: (Ord k, Monad m) => k -> Tables k (Deferred m v) -> (Maybe (m v), Tables k (Deferred m v))
    takeTables k (Tables xs) = (get Alt a, Tables xs')
      where
        (a, xs') = foldMap f (zip (iterate succ mempty) xs)
      
        f (i, x) = let (m, x') = takeTable k x in (Alt (do{ Deferred w <- m; return (Deferred (tell i >> w)) }, [x'])
        
    takeTable :: Ord k => k -> Table k v -> (Maybe v, Table k v)
    takeTable k (Table x) = let (a, x') = M.updateLookupWithKey (\ _ _ -> Nothing) k x in (a, Table x')
    
deleteTables :: (Show k, Ord k, MonadError E.Error m) => Deferred m k -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
deleteTables k = alterTables k id

showTables :: Show k => Tables k v -> String
showTables (Tables xs) = foldMap (\ (i, x) -> show i++":"++show x) (zip (iterate (+1) 1) xs)

instance Show k => Show (Tables k v) where show = showTables


-- Scope
type IOExcept = ExceptT E.Error IO
type Self = Tables (T.Name Value) (Deferred IOExcept Value)
type Env = Table T.Ident (Deferred IOExcept Value)
type DE = Deferred IOExcept
type ERT = ReaderT (NonEmpty Env)
type SRT = ReaderT (NonEmpty Self)
type ESRT m = ERT (SRT m)
type ESR = ESRT Identity

liftToESRT :: Monad m => m a -> ESRT m a
liftToESRT = lift . lift

mapESRT :: (m a -> n b) -> ESRT m a -> ESRT n b
mapESRT = mapReaderT . mapReaderT

runESRT :: ESRT m a -> m a
runESRT m = runReaderT (runReaderT m (primitiveBindings, [])) (emptyTables,[])

lookupSelf :: T.Name Value -> ESRT DE Value
lookupSelf k =
  do{ selfs <- lift ask
    ; let mv = getAlt (foldMap (Alt . lookupTables k) selfs)
    ; maybe (throwUnboundVar k) liftToESRT mv
    } 

lookupEnv :: T.Ident -> ESRT DE Value
lookupEnv k =
  do{ envs <- ask
    ; let mv = getAlt (foldMap (Alt . lookupTable k) envs)
    ; maybe (throwUnboundVar k) liftToESRT mv
    }

lookupValue :: T.Name Value -> Value -> DE Value
lookupValue k v =
  do{ selfs <- lift (configureSelf (unNode v))
    ; let mv = getAlt (foldMap (Alt . lookupTables k) selfs)
    ; maybe (throwUnboundVar k) id mv
    }
    

-- EndoM
newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM return
  EndoM f `mappend` EndoM g = EndoM (f <=< g)
  
type Endo = EndoM Identity

endo :: (a -> a) -> Endo a
endo f = EndoM (Identity . f)

appEndo :: Endo a -> (a -> a)
appEndo (EndoM f) = runIdentity . f

-- Scope :: (Self -> Env) -> (Self -> Env) -> (Self -> Env, Classed)
-- Classed :: Self -> Self -> IOExcept Self
--type Scope = EndoM (ReaderT ER (Writer Classed)) ER
--type Classed = EndoM (SRT IOExcept) Self
type ScopeMono = NonEmpty Env -> NonEmpty Self -> (Endo Env, EndoM IOExcept Self)
type Scope = Endo (NonEmpty Env -> ReaderT (NonEmpty Self) (Writer (NonEmpty Self)) (NonEmpty Env))
type Classed = Endo (NonEmpty Self -> IOExcept (NonEmpty Self))

initial :: Monad m => a -> Endo m a
initial a = Endo (const (return a))

scopeEndo :: ScopeMono -> Scope
scopeEndo scope =
  Endo (\ envs -> 
    do{ selfs <- ask
      ; let (f, g) = scope envs selfs
      ; lift (writer (fix (appEndo f) :| tail envs, do{ self <- mfix g; return (self :| tail selfs) }))
      })

initialSelf :: Self -> EndoM IOExcept Self
initialSelf a = EndoM (return (const a))
      

scopeMono :: ESR (Env -> Env, Self -> IOExcept Self) -> ScopeMono
scopeMono m envs selfs = let (f, g) = runReader (runReaderT m envs) selfs in (endo f, EndoM g)

configureScope :: Scope -> Classed
configureScope scope = Endo (execWriter . runReaderT (mfix scope))


-- Ided
newtype Id = Id { getId :: Integer } deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
newtype Ided a = Ided (State Ids a) deriving (Functor, Applicative, Monad, MonadState Ids)

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))

runIded :: Ided a -> a    
runIded (Ided m) = evalState m (Id `fmap` iterate (+1) 0)

-- Value
type Node = Classed

emptyNode :: Node
emptyNode = mempty

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
    f (Symbol _) = fromSelf $ emptyTables
    f (BuiltinSymbol _) = fromSelf $ emptyTables
    
    fromSelf :: Self -> Node
    fromSelf = initialSelf

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptyTables

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptyTables

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptyTables

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

primitiveBindings :: Table k v
primitiveBindings = emptyTable

