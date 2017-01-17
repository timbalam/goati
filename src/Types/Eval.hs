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
 
import qualified Types.Parser as T
import qualified Error as E
  
type IOExcept = ExceptT E.Error IO
data Vtable = Vtable [(T.Name Value, IOClassed Value)]
type Self = Vtable
type Env = IOClassed Vtable
type Classed = ReaderT Self
type IOClassed = Classed IOExcept
type Scoped = ReaderT Env
type Scoped' = Scoped Identity
type Eval = State Integer
type Super = Vtable

liftIO :: IO a -> IOExcept a
liftIO = lift

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

throwUnboundVar :: Show k => k -> IOClassed a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: IOExcept a -> IOExcept a -> IOExcept a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: IOExcept a -> E.Error -> IOExcept a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

emptyVtable :: Vtable
emptyVtable = Vtable []

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs++ys)
 
lookupVtable :: T.Name Value -> Vtable -> IOClassed Value
lookupVtable k (Vtable ys) = 
  maybe
    (throwUnboundVar $ k)
    id
    (k `lookup` ys)

insertVtable :: T.Name Value -> IOClassed Value -> Vtable -> Vtable
insertVtable k vr (Vtable xs) = Vtable $ (k, vr):xs

deleteVtable :: T.Name Value -> Vtable -> Vtable
deleteVtable k = insertVtable k (throwUnboundVar k)

showVtable :: Vtable -> String
showVtable (Vtable xs) = show (map fst xs)

bindClassed :: Monad m => Classed m Vtable -> Classed m Vtable
bindClassed vr =
  do{ Vtable xs <- vr
    ; self <- askClassed
    ; return . Vtable $ map ( \(k, vf) -> (k, local (const self) vf) ) xs
    }
    
withSelf :: Self -> Env
withSelf (Vtable xs) =
  do{ self' <- askClassed
    ; return . Vtable $ map ( \(k, vf) -> (k, lookupVtable k self') ) xs
    }

mapClassed = mapReaderT
runClassed = runReaderT

askClassed :: Monad m => Classed m Self
askClassed = ask

liftClassed :: Monad m => m a -> Classed m a
liftClassed = lift

lookupSelf :: T.Name Value -> IOClassed Value
lookupSelf k = askClassed >>= lookupVtable k

showSelf :: IOClassed ()
showSelf = askClassed >>= liftClassed . liftIO . putStrLn . showVtable
   
mapScoped = mapReaderT   
runScoped = runReaderT

askScoped :: Monad m => Scoped m Env
askScoped = ask

liftScoped :: Monad m => m a -> Scoped m a
liftScoped = lift
    
lookupEnv :: T.Name Value -> Scoped IOClassed Value
lookupEnv k = askScoped >>= lift >>= liftScoped . lookupVtable k

showEnv :: Scoped IOClassed ()
showEnv = askScoped >>= lift >>= liftScoped . liftClassed . liftIO . putStrLn . showVtable

runValue :: Scoped IOClassed Value -> IOExcept Value
runValue vf = (runClassed . runScoped vf) (return primitiveBindings) emptyVtable

runValue_ :: Scoped IOClassed Value -> IOExcept ()
runValue_ vf = runValue vf >> return ()
    
runEval :: Eval a -> a
runEval m = evalState m 0

data Value = String String | Number Double | Bool Bool | Node Integer (Super -> Self) | Symbol Integer | BuiltinSymbol BuiltinSymbol
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
  
  
newNode :: Eval ((Super -> Self) -> Value)
newNode =
  do{ i <- get
    ; modify' (+1)
    ; return (Node i)
    }
    
unNode :: Value -> Super -> Self
unNode = f
  where
    f (String x) = fromSelf $ primitiveStringSelf x
    f (Number x) = fromSelf $ primitiveNumberSelf x
    f (Bool x) = fromSelf $ primitiveBoolSelf x
    f (Node _ vs) = vs
    f (Symbol _) = fromSelf $ emptyVtable
    f (BuiltinSymbol _) = fromSelf $ emptyVtable
    fromSelf = concatVtable

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

primitiveBindings :: Vtable
primitiveBindings = emptyVtable

