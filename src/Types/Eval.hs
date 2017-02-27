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
import Control.Monad.Trans.State
  ( StateT
  , evalStateT
  , mapStateT
  , get
  , put
  , modify'
  )
import Control.Monad.IO.Class( liftIO )
import Control.Monad.Trans.Reader
  ( ReaderT(ReaderT)
  , runReaderT
  , mapReaderT
  , ask
  , local
  , Reader
  , runReader
  , mapReader
  )
import Control.Monad.Identity ( Identity, runIdentity )
import Control.Monad.Trans.Class( lift )
import Control.Applicative( (<|>) )
import Control.Monad.Trans.Free
  ( FreeF(..)
  , FreeT(..)
  , liftF
  , transFreeT
  , retractT
  , hoistFreeT
  )
import Data.Maybe
  ( isJust
  , mapMaybe
  , catMaybes
  )
import Data.Traversable( forM, for )
import qualified Data.Map as M
import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  
type IOExcept = ExceptT E.Error IO
data Vtable k = Vtable (M.Map k (IOClasses Value))
type Self = Vtable (T.Name Value)
type Classes = FreeT (Reader Self)
type IOClasses = Classes IOExcept
type Env = IOClasses (Vtable T.Ident)
type Scoped = Reader Env
type Eval = State Integer
type DiffList k a = [(k, a -> a)] 
type Node = [IOClasses (DiffList (T.Name Value) (IOClasses Value))]
type EnvNode = DiffList T.Ident (IOClasses Value)

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

emptyVtable :: Vtable k
emptyVtable = Vtable M.empty

concatVtable :: Ord k => Vtable k -> Vtable k -> Vtable k
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs `M.union` ys)

lookupVtable :: (Ord k, Show k) => k -> Vtable k -> IOClasses Value
lookupVtable k (Vtable ys) = M.findWithDefault (throwUnboundVar k) k ys

insertVtable :: Ord k => k -> IOClasses Value -> Vtable k -> Vtable k
insertVtable k vr (Vtable xs) = Vtable (M.insert k vr xs)

alterVtable :: (Ord k, Show k) => (IOClasses Value -> IOClasses Value) -> k -> Vtable k -> Vtable k
alterVtable f k (Vtable xs) = Vtable (M.alter f' k xs)
  where
    f' = Just . f . maybe (throwUnboundVar k) id

deleteVtable :: Ord k => k -> Vtable k -> Vtable k
deleteVtable k (Vtable xs) = Vtable (M.delete k xs)

showVtable :: Show k => Vtable k -> String
showVtable (Vtable xs) = show (M.keys xs)

fromDiffList :: (Ord k, Show k) => DiffList k (IOClasses Value) -> Vtable k
fromDiffList = Vtable . M.mapWithKey (\ k f -> f (throwUnboundVar k)) . M.fromListWith (flip (.))

toDiffList :: Vtable k -> DiffList k (IOClasses Value)
toDiffList (Vtable xs) = M.toList (M.map const xs)

mapClasses :: Monad m => (forall a. m a -> n a) -> Classes m a -> Classes n a
mapClasses = hoistFreeT
runClass = runFreeT

runClasses :: Monad m => Classes m a -> Self -> m a
runClasses m self = runReaderT (retractT tm) self
  where
    tm = transFreeT (mapReaderT (return . runIdentity)) m
    
askClasses :: Monad m => Classes m Self
askClasses = liftF ask

liftClasses :: Monad m => m a -> Classes m a
liftClasses = lift

bindClasses :: Monad m => Classes m (Vtable k) -> Classes m (Vtable k)
bindClasses vr =
  do{ Vtable xs <- vr
    ; self <- askClasses
    ; return . Vtable . M.map (liftClasses . flip runClasses self) $ xs
    }
    
withNode :: Node -> Env
withNode node =
  do{ keys <- mapMaybe (maybeRef . fst) . concat <$> sequence node
    ; self <- askClasses
    ; return . Vtable . M.fromSet (flip lookupVtable self . T.Ref) . S.fromList $ keys
    }
  where
    maybeRef (T.Ref x) = Just x
    maybeRef (T.Key _) = Nothing

lookupSelf :: T.Name Value -> IOClasses Value
lookupSelf k = askClasses >>= lookupVtable k
    

putSelf :: IOClasses ()
putSelf = askClasses >>= liftIO . putStrLn . showVtable

deletes :: Show k => k -> IOClasses Value -> IOClasses Value
deletes k  = const (throwUnboundVar k)
   
mapScoped = mapReader
runScoped = runReader

askScoped :: Scoped Env
askScoped = ask
    
lookupEnv :: T.Ident -> Scoped (IOClasses Value)
lookupEnv k = askScoped >>= return . (>>= lookupVtable k)

putEnv :: Scoped (IOClasses ())
putEnv = askScoped >>= return . (>>= liftIO . putStrLn . showVtable)

runValue :: Scoped (IOClasses Value) -> IOExcept Value
runValue vf = runClasses (runScoped vf (return primitiveBindings)) emptyVtable

runValue_ :: Scoped (IOClasses Value) -> IOExcept ()
runValue_ vf = runValue vf >> return ()
    
mapEval = mapState
runEval m = evalState m 0

zipClasses :: (Monad m, Applicative f) => FreeT f m (a -> b) -> FreeT f m a -> FreeT f m b
FreeT mf `zipClasses` FreeT ma = FreeT $ zipF <$> mf <*> ma
  where
    zipF :: (Monad m, Applicative f) => FreeF f (a -> b) (FreeT f m (a -> b)) -> FreeF f a (FreeT f m a) -> FreeF f b (FreeT f m b) 
    Free fmf `zipF` Free fma = Free (zipClasses <$> fmf <*> fma)
    Free fmf `zipF` Pure a =  Free (fmap ($ a) <$> fmf)
    Pure f `zipF` Free fma = Free (fmap f <$> fma)
    Pure f `zipF` Pure a = Pure (f a)

  
unF :: (Applicative f, Applicative m) => FreeF f a (m a) -> f (m a)
unF (Pure a) = pure (pure a)
unF (Free f) = f

execNode :: Node -> IOExcept Self
execNode = go
  where
    go :: Node -> IOExcept Self
    go node =
      do{ dones <- mapM (fmap maybeDone . runFreeT) node
        ; noder <- mapM unF <$> mapM runFreeT node
        ; let self = fromDiffList . concat $ (catMaybes dones)
        ; if all isJust dones then return self else go (runReader noder self)
        }
        
    maybeDone :: FreeF f a b -> Maybe a
    maybeDone (Pure a) = Just a
    maybeDone _ = Nothing
  

data Value = String String | Number Double | Bool Bool | Node Integer Node | Symbol Integer | BuiltinSymbol BuiltinSymbol
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
  
  
newNode :: Eval (Node -> Value)
newNode =
  do{ i <- get
    ; modify' (+1)
    ; return (Node i)
    }
    
unNode :: Value -> Node
unNode = f
  where
    f (String x) = fromSelf $ primitiveStringSelf x
    f (Number x) = fromSelf $ primitiveNumberSelf x
    f (Bool x) = fromSelf $ primitiveBoolSelf x
    f (Node _ vs) = vs
    f (Symbol _) = fromSelf $ emptyVtable
    f (BuiltinSymbol _) = fromSelf $ emptyVtable
    fromSelf x = map (return . pure) (toDiffList x)

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptyVtable

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptyVtable

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptyVtable

newSymbol :: Eval Value
newSymbol =
  do{ i <- get
    ; modify' (+1)
    ; return (Symbol i)
    }

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


undefinedNumberOp :: Show s => s -> IOExcept a
undefinedNumberOp s = throwError $ E.PrimitiveOperation "Operation undefined for numbers" (show s)

undefinedBoolOp :: Show s => s -> IOExcept a
undefinedBoolOp s = throwError $ E.PrimitiveOperation "Operation undefined for booleans" (show s)

primitiveNumberUnop :: T.Unop -> Double -> IOExcept Value
primitiveNumberUnop (T.Neg) x = return . Number $ negate x
primitiveNumberUnop s       _ = undefinedNumberOp s

primitiveBoolUnop :: T.Unop -> Bool -> IOExcept Value
primitiveBoolUnop (T.Not) x = return . Bool $ not x
primitiveBoolUnop s       _ = undefinedBoolOp s

primitiveNumberBinop :: T.Binop -> Double -> Double -> IOExcept Value
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

primitiveBoolBinop :: T.Binop -> Bool -> Bool -> IOExcept Value
primitiveBoolBinop (T.And) x y = return . Bool $ x && y
primitiveBoolBinop (T.Or)  x y = return . Bool $ x || y
primitiveBoolBinop (T.Lt)  x y = return . Bool $ x < y
primitiveBoolBinop (T.Gt)  x y = return . Bool $ x > y
primitiveBoolBinop (T.Eq)  x y = return . Bool $ x == y
primitiveBoolBinop (T.Ne)  x y = return . Bool $ x /= y
primitiveBoolBinop (T.Le)  x y = return . Bool $ x <= y
primitiveBoolBinop (T.Ge)  x y = return . Bool $ x >= y
primitiveBoolBinop s       _ _ = undefinedBoolOp s

primitiveBindings :: Vtable T.Ident
primitiveBindings = emptyVtable

