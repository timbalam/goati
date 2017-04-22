{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving #-}

module Types.Eval
  where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer
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
import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  

-- Error
throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err


-- Tables
newtype Deferred m a = Deferred (WriterT (Max Word) m a) deriving (Functor, Applicative, Monad, Traversable, MonadTrans, MonadError, MonadIO)

undefer :: Monad m => Deferred m a -> m a
undefer (Deferred w) = do{ (a, _) <- runWriter w; return a }

deferred :: Monad m => (Max Word, a) -> Deferred m a
deferred = Deferred . writer

newtype Table k v = Table (M.Map k v)
newtype Tables k v = Tables [Table k v]

emptyTable :: Table k v
emptyTable = Table M.empty

lookupTable :: Ord k => k -> Table k v -> Maybe v
lookupTable k (Table x) = M.lookup k x

insertTable :: Ord k => k -> v -> Table k v -> Table k v
insertTable k v (Table x) = Table (M.insert k v x)

alterTable :: Ord k => v -> k -> (v -> v) -> Table k v -> Table k v
alterTable v k f (Table x) = Table (M.alter (Just . f . maybe v id) k x)

deleteTable :: Ord k => k -> Table k v -> Table k v
deleteTable k (Table x) = Table (M.delete k x)

unionTable :: Ord k => Table k v -> Table k v -> Table k v
unionTable (Table x) (Table y) = Table (M.union x y)

differenceTable :: Ord k => Table k v -> Table k v -> Table k v
differenceTable (Table x) (Table y) = Table (M.difference x y)

showTable :: Show k => Table k v -> String
showTable (Table x) = show (M.keys x)

instance Show k => Show (Table k v) where show = showTable

emptyTables :: Tables k v
emptyTables = Tables []

lookupTables :: (Ord k, Monad m) => k -> Tables k (Deferred m v) -> Maybe (Deferred m v)
-- M.lookup :: k -> Map k v -> Maybe v
lookupTables k (Tables xs) = getLast (foldMap f (zip (iterate succ mempty) xs))
  where
    f (i, x) = Last (do{ a <- lookupTable; return (i, a) })

insertTables :: (Ord k, Monad m) => Deferred m k -> Deferred m v -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
-- M.insert :: k -> v -> Map k v -> Map k v
insertTables (Deferred w) v (Tables xs) =
  do{ (k, i) <- runWriter w
    ; let
        go i [] = go i [emptyTable]
        go i (x:xs) =
          | i==minBound = (insertTable k v x):(deleteTable k <$> xs)
          | otherwise = x:(go (pred i) xs)
    ; return (Tables (go i xs))
    }   
      
alterTables :: (Ord k, Monad m) => Deferred m v -> Deferred m k -> (Deferred m v -> Deferred m v) -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
alterTables mv (Deferred w) f t =
  do{ (k, i) <- runWriter w
    ; let mv' = f (maybe mv id (lookupTables k t)) 
    ; insertTables (Deferred (writer (k, i))) mv' t
    }
    
unionTables :: (Ord k, Monad m) => Deferred m (Tables k (Deferred m v)) -> Tables k (Deferred m v) -> m (Tables k (Deferred m v))
unionTables (Deferred w) (Tables ys) =
  do{ (Tables xs, i) <- runWriter w
    ; let
        go i w xs [] = go i w xs [emptyTable]
        go _ w [] ys = flip differenceTable w <$> ys
        go i w (x:xs) (y:ys) = 
          | i==minBound = (unionTable x (difference y w)):(go i (unionTable w x) xs ys)
          | otherwise = (difference y w):(go (pred i) w xs ys)
    ; return (Tables (go i emptyTable xs ys))
    }

showTables :: Show k => Tables k v -> String
showTables (Tables xs) = foldMap (\ (i, x) -> show i++":"++show x) (zip (iterate (+1) 1) xs)

instance Show k => Show (Tables k v) where show = showTables


-- Scope
type IOExcept = ExceptT IO
type Self = Tables (T.Name Value) (Deferred IOExcept Value)
type Env = Table T.Ident (Deferred IOExcept Value)
type DE = Deferred IOExcept
type E = Reader Self Env
type ERT = ReaderT E
type ER = ERT Identity
type SRT = ReaderT Self
type ESRT m = ERT (SRT m)
type ESR = ESRT Identity

liftToESRT :: m a -> ESRT m a
liftToESRT = lift . lift

mapESRT :: (m a -> n b) -> ESRT m a -> ESRT n b
mapESRT f = mapReaderT . mapReaderT f

askEnv :: ESRT DE Env
askEnv = runReader <$> ask <*> lift ask

lookupSelf :: T.Name Value -> ESRT DE Value
lookupSelf k = do{ self <- lift ask; maybe (throwUnboundVar k) liftToESRT (lookupTables k self) }

lookupEnv :: T.Ident -> ESRT DE Value
lookupEnv k = do{ env <- askEnv; maybe (throwUnboundVar k) liftToESRT (lookupTable k env) }

lookupValue :: T.Name Value -> Value -> DE Value
lookupValue k v =
  do{ self <- lift (configureSelf (unNode v <> initial emptyTables))
    ; maybe (throwUnboundVar k) id (lookupTables (return k) self)
    }
    

-- EndoM
newtype EndoM m a = EndoM { getEndoM :: a -> m a }

instance Monad m => Monoid (EndoM m a) where
  mempty = pure
  f `mappend` g = f <=< g
  
newtype Endo = EndoM Identity

endo :: (a -> a) -> Endo a
endo f = EndoM (Identity . f)


configure :: MonadFix m => (super -> m self) -> EndoM (ReaderT self m) super -> m self
-- mfix :: (super -> (ReaderT self m) super) -> (ReaderT self m) super
-- runReaderT :: ReaderT self m super -> self -> m super
configure f (EndoM g) = mfix (lift . f =<< runReaderT (mfix g))

initial :: Monad m => super -> EndoM (ReaderT self m) super
initial = EndoM . return

-- Scope :: (Self -> Env) -> (Self -> Env) -> (Self -> Env, Classed)
-- Classed :: Self -> Self -> IOExcept Self
newtype Scope = EndoM (ReaderT ER (Writer Classed)) ER
newtype Classed = EndoM (SRT IOExcept) Self

configureEnv :: Scope -> Classed
configureEnv (Endo f) = sr
  where
    (er, sr) = runWriter (runReaderT (mfix f) er)

configureSelf :: Classed -> IOExcept Self
configureSelf f = mfix (runReaderT (mfix f))

scope :: ESR (Env -> Env, Self -> IOExcept Self) -> Scope
scope m = Endo (\ esuperr ->
  -- flip mapReaderT m :: (SRT DE a -> Writer Classed ER) -> ReaderT ER (Writer Classed) ER
  flip mapReaderT m (\ pr ->
      esuperr' = fst <$> pr <*> esuperr
      
      classed = Endo (\ ssuper -> mapReaderT runIdentity (snd <$> pr <*> pure ssuper))
    in
      writer (esuperr', classed)))

-- Ided
newtype Id = Id { getId :: Integer } deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
newtype Ided = Ided (State Ids) deriving (Functor, Applicative, Monad, MonadState Ids)

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))
    
runIded m = evalStateT m (Id `fmap` iterate (+1) 0)



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
    fromSelf r = EndoM (return r)

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

primitiveBindings :: Table k v m
primitiveBindings = emptyTable

