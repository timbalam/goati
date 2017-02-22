module Types.Eval
  where
import Control.Monad.Except
  ( ExceptT
  , runExceptT
  , throwError
  , catchError
  )
import Control.Monad.Trans.State
  ( State
  , get
  , put
  , modify'
  , evalState
  )
import Control.Monad.Trans.Reader
  ( ReaderT(ReaderT)
  , runReaderT
  , mapReaderT
  , ask
  , local
  )
import Control.Monad.Identity ( Identity )
import Control.Monad.Trans.Class( lift )
import Control.Applicative( (<|>) )
import Control.Monad.Trans.Free
  ( FreeF(..)
  , FreeT(..)
  , liftF
  )
import qualified Data.Map as M
 
import qualified Types.Parser as T
import qualified Error as E
  
type IOExcept = ExceptT E.Error IO
data Vtable = Vtable { unVtable :: M.Map (T.Name Value) (IOClasses Value) }
type Self = Vtable
type Classes = FreeT (Reader Self)
type IOClasses = Classes IOExcept
type Env = IOClasses Vtable
type Scoped = Reader Env
type Eval = StateT Integer
type Node = Edges IOExcept Self
type Edges m a = [Edge m a]
type Edge m a = IOClasses (a -> m a)

liftIO :: MonadIO m => IO a -> m a
liftIO = lift

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

emptyVtable :: Vtable
emptyVtable = Vtable M.empty

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs `M.union` ys)

lookupVtable :: T.Name Value -> Vtable -> IOClasses Value
lookupVtable k (Vtable ys) = 
  maybe
    (throwUnboundVar $ k)
    id
    (k `M.lookup` ys)

insertVtable :: T.Name Value -> IOClasses Value -> Vtable -> Vtable
insertVtable k vr (Vtable xs) = Vtable (M.insert k vr xs)

deleteVtable :: T.Name Value -> Vtable -> Vtable
deleteVtable k (Vtable xs) = Vtable (k `M.delete` xs)
--deleteVtable k = insertVtable k (throwUnboundVar k)

showVtable :: Vtable -> String
showVtable (Vtable xs) = show (map fst xs)

mapClasses = hoistFreeT
runClass = runFreeT

runClasses :: Classes m a -> Vtable -> m a
runClasses m v = runReaderT (retractT tm) v
  where
    tm = transFreeT (mapReaderT (return . runIdentity)) m

askClasses :: Monad m => Classes m Self
askClasses = liftF ask

liftClasses :: Monad m => m a -> Classes m a
liftClasses = lift

bindClasses :: Monad m => Classes m Vtable -> Classes m Vtable
bindClasses vr =
  do{ Vtable xs <- vr
    ; self <- askClasses
    ; return . Vtable $ map (lift . flip runClasses self) xs
    }
  where
    
withSelf :: Self -> Env
withSelf (Vtable xs) =
  do{ self' <- askClasses
    ; return . Vtable $ mapWithKey (const . flip lookupVtable self') xs
    }

lookupSelf :: T.Name Value -> IOClasses Value
lookupSelf k = askClasses >>= lookupVtable k

showSelf :: IOClasses ()
showSelf = askClasses >>= liftIO . putStrLn . showVtable
   
mapScoped = mapReader
runScoped = runReader

askScoped :: Scoped Env
askScoped = ask
    
lookupEnv :: T.Name Value -> Scoped (IOClasses Value)
lookupEnv k = askScoped >>= return . (>>= lookupVtable k)

showEnv :: Scoped (IOClasses ())
showEnv = askScoped >>= return . (>>= liftIO . putStrLn . showVtable)

runValue :: Scoped (IOClasses Value) -> IOExcept Value
runValue vf = runClasses (runScoped vf (return primitiveBindings)) emptyVtable

runValue_ :: Scoped (IOClasses Value) -> IOExcept ()
runValue_ vf = runValue vf >> return ()
    
mapEval = mapStateT
runEval m = evalStateT m 0

liftEval :: Monad m => m a -> Eval m a
liftEval = lift

unClass :: Monad m => Classes m a -> m (Reader Self (Classes m a))
unClass m = runFreeT m >>= unF
  where
    unF :: FreeF (Reader Self) a (Classes m a) -> Reader Self (Classes m a)
    unF (Pure a) = return (Pure a)
    unF (Free f) = f
  
liftClasses :: Functor m => m a -> Classes m a
liftClasses = liftF

zipClasses :: Applicative m => Classes m (a -> b) -> Classes m a -> Classes m b
FreeT mf `zipClasses` FreeT ma = FreeT $ zipF <$> mf <*> ma
  where
    zipF :: Applicative m => FreeF (Reader Self) (a -> b) (Classes m (a -> b)) -> FreeF (Reader Self) a (Classes m a) -> FreeF (Reader Self) b (Classes m b) 
    Free mf `zipF` Free ma = Free $ mf <*> ma
    Free mf `zipF` Pure a =  Free $ mf <*> return (Pure a)
    Pure f `zipF` Free ma = Free $ return (Pure f) <*> ma
    Pure f `zipF` Pure a = Pure (f a)
sf `zipClasses` sa = sf <*> sa

stageVtable :: Vtable -> Edges
stageVtable v = [return . M.union v]

inserts :: IOClasses (T.Name Value) -> IOClasses Value -> Edge
inserts kr vr = flip insertVtable vr <$> kr

deletes :: IOClasses (T.Name Value) -> Edge
deletes kr = return . deleteVtable <$> kr

execEdges :: Monad m => Edges m a -> a -> m a
execEdges es a = go es
  where
    go es =
      do{ dones <- mapM ((maybeDone <$>) . runFreeT) es
        ; let self' = foldr (>>=) return (catMaybes dones) a
              -- IOClasses (a -> m a) -> Reader Self (IOClasses (a -> m a))
              mvs' = mapM unClass es
        ; if all isJust dones then return self' else runReader mvs' self' >>= go  
        }
        
    maybeDone :: FreeF f a b -> Maybe a
    maybeDone (Pure k) = Just k
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
  
  
newNode :: Monad m => Eval m (Node -> Value)
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
    fromSelf x = [stageVtable x]

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptyVtable

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptyVtable

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptyVtable

newSymbol :: Monad m => Eval m Value
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

primitiveBindings :: Vtable
primitiveBindings = emptyVtable

