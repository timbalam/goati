{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving, DeriveTraversable #-}

module Types.Eval
  where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding
  ( Endo(Endo)
  , appEndo
  , Last(Last)
  , getLast
  )
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
import Data.Semigroup ( Max(Max), Last(Last), Option(Option), getOption, getLast )
--import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Set as S
import Data.IORef
 
import qualified Types.Parser as T
import qualified Error as E
  

-- Error
throwUnboundVarIn :: (Show k, MonadError E.Error m) => k -> M.Map k v -> m a
throwUnboundVarIn k x = throwError (E.UnboundVar ("Unbound var in "++show (M.keys x)) (show k))

throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError (E.UnboundVar "Unbound var" (show k))

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v dft = catchError v (handleUnboundVar dft)
  where
    handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
    handleUnboundVar a (E.UnboundVar _ _) = a
    handleUnboundVar _ err = throwError err
    
maybeCatchUnboundVar :: MonadError E.Error m => m a -> Maybe (m a) -> m a
maybeCatchUnboundVar v mb = catchUnboundVar v (maybe v id mb)

throwOverlappingDefinitions :: (Show k, MonadError E.Error m) => k -> m a
throwOverlappingDefinitions k = throwError (E.OverlappingDefinitions "Overlapping definitions for var" (show k))

-- Env / Self
type I = Ided Identity
type X = ExceptT E.Error IO
type IX = Ided X
type Cell = IORef (IX Value)
type Self = M.Map (T.Name Value) Cell
type Env = M.Map T.Ident Cell
type ERT = ReaderT Env
type SRT = ReaderT Self
type ESRT = ReaderT (Env, Self)

emptySelf = M.empty

newCell :: MonadIO m => v -> m (IORef v)
newCell = liftIO . newIORef

viewCell :: MonadIO m => IORef (m v) -> m v
viewCell ref =
  do{ v <- join (liftIO (readIORef ref))
    ; liftIO (writeIORef ref (return v))
    ; return v
    }

viewCellAt :: (MonadError E.Error m, MonadIO m, Ord k, Show k) => k -> M.Map k (IORef (m v)) -> m v
viewCellAt k x = maybe (throwUnboundVarIn k x) viewCell (M.lookup k x)

viewEnvAt :: T.Ident -> ESRT IX Value
viewEnvAt k =
  do{ (env, _) <- ask
    ; maybe (throwUnboundVar k) (lift . viewCell) (M.lookup k env)
    }
    
viewSelfAt :: T.Name Value -> ESRT IX Value
viewSelfAt k =
 do{ (_, self) <- ask
   ; maybe (throwUnboundVar k) (lift . viewCell) (M.lookup k self)
   }

viewValue :: Value -> IX Self
viewValue (Node _ ref c) =
  liftIO (readIORef ref) >>= 
    maybe 
      (do{ self <- configureClassed c
         ; liftIO (writeIORef ref (Just self))
         ; return self })
      return
viewValue x = configureClassed (unNode x)

valueAtMaybe :: T.Name Value -> (Maybe Cell -> IX (Maybe Cell)) -> Maybe (IX Value) -> IX Value
valueAtMaybe k f mb =
  do{ c <- maybe (return mempty) (>>= return . unNode) mb
    ; newNode <*> pure (EndoM (lift . M.alterF f k) <> c)
    }

valueAt :: (MonadState Ids m, MonadIO m) => T.Name Value -> (Maybe Cell -> IX (Maybe Cell)) -> Value -> m Value
valueAt k f v = newNode <*> pure (EndoM (lift . M.alterF f k) <> unNode v)

cellAtMaybe :: MonadIO m => T.Name Value -> (Maybe Cell -> IX (Maybe Cell)) -> Maybe Cell -> m Cell
cellAtMaybe k f Nothing = liftIO (newIORef (valueAtMaybe k f Nothing))
cellAtMaybe k f (Just ref) = cellAt k f ref

cellAt :: MonadIO m => T.Name Value -> (Maybe Cell -> IX (Maybe Cell)) -> Cell -> m Cell
cellAt k f ref =
  liftIO
    (do{ mv <- readIORef ref
       ; newIORef (mv >>= valueAt k f)
       })

runESRT :: Monad m => ESRT m a -> m a
runESRT m = runReaderT m (primitiveBindings, M.empty)
    

-- EndoM
newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM return
  EndoM f `mappend` EndoM g = EndoM (f <=< g)
  
type Endo = EndoM Identity

endo :: Monad m => (a -> a) -> EndoM m a
endo f = EndoM (return . f)

appEndo :: Endo a -> (a -> a)
appEndo (EndoM f) = runIdentity . f

-- Scope
type ScopeB = (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env
type Scope = EndoM (ERT (SRT (WriterT (EndoM IX Self) IX))) Env
type Classed = EndoM (SRT IX) Self

initial :: Monad m => a -> EndoM m a
initial a = EndoM (const (return a))

configure :: MonadFix m => (super -> m self) -> EndoM (ReaderT self m) super -> m self
configure f (EndoM g) = mfix (runReaderT (mfix g >>= lift . f))

buildScope :: ScopeB -> Scope
buildScope scopeBuilder =
  EndoM (\ env0 -> 
    do{ env <- ask
      ; self <- lift ask
      ; let EndoM f = scopeBuilder (env, self)
      ; lift (lift (f env0))
      })
      
configureScope :: Scope -> Classed
configureScope scope =
  EndoM
    (\ self0 ->
       do{ let
             mscope :: SRT (WriterT (EndoM IX Self) IX) Env
             mscope = configure return (scope <> initial M.empty)
             
             mendo :: SRT IX (EndoM IX Self)
             mendo = mapReaderT execWriterT mscope
         ; EndoM f <- mendo
         ; lift (f self0)
         })
         
configureClassed :: Classed -> IX Self
configureClassed c = configure return (c <> initial M.empty)


-- Ided
newtype Id = Id { getId :: Word } deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
newtype Ided m a = Ided (StateT Ids m a) deriving (Functor, Applicative, Monad, MonadState Ids, MonadIO, MonadTrans, MonadError e, MonadWriter w, MonadReader r, MonadFix)

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))

runIded :: Monad m => Ided m a -> m a    
runIded (Ided m) = evalStateT m (Id `fmap` iterate succ 0)

-- Value
type Node = Classed

emptyNode :: Node
emptyNode = mempty

data Value = String String | Number Double | Bool Bool | Node Id (IORef (Maybe Self)) Node | Symbol Id | BuiltinSymbol BuiltinSymbol
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
  show (Node i _ _) = "<Node:" ++ show i ++ ">"
  show (Symbol i) = "<Symbol:" ++ show i ++ ">"
  show (BuiltinSymbol x) = show x

instance Eq Value where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Bool x == Bool x' = x == x'
  Node x _ _ == Node x' _ _ = x == x'
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
  compare (Node x _ _)      (Node x' _ _)      = compare x x'
  compare (Node _ _ _)      _                  = LT
  compare _                 (Node _ _ _)       = GT
  compare (Symbol x)        (Symbol x')        = compare x x'
  compare (Symbol _)        _                  = LT
  compare _                 (Symbol _)         = GT
  compare (BuiltinSymbol x) (BuiltinSymbol x') = compare x x'
  
  
newNode :: (MonadState Ids m, MonadIO m) => m (Node -> Value)
newNode = useId Node <*> liftIO (newIORef Nothing)
    
unNode :: Value -> Node
unNode = go
  where
    go (String x) = fromSelf $ primitiveStringSelf x
    go (Number x) = fromSelf $ primitiveNumberSelf x
    go (Bool x) = fromSelf $ primitiveBoolSelf x
    go (Node _ _ c) = c
    go (Symbol _) = fromSelf $ emptySelf
    go (BuiltinSymbol _) = fromSelf $ emptySelf
    
    fromSelf :: Self -> Node
    fromSelf self = initial self
    
    refKey :: T.Name Value -> Maybe T.Ident
    refKey (T.Key _) = Nothing
    refKey (T.Ref x) = Just x

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptySelf

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptySelf

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptySelf

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

primitiveBindings :: Env
primitiveBindings = M.empty

