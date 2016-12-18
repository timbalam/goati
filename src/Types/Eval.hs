module Types.Eval
  ( IOExcept
  , liftIO
  , Vtable
  , emptyVtable
  , insertVtable
  , lookupEnv
  , lookupVtable
  , Vtables
  , emptyVtables
  , inserts
  , concats
  , unpacks
  , Env
  , Value(String, Number, Bool)
  , newNode
  , unNode
  , newSymbol
  , Eval
  , runEval
  , selfSymbol
  , resultSymbol
  , rhsSymbol
  , unopSymbol
  , primitiveBoolUnop
  , primitiveNumberUnop
  , binopSymbol
  , primitiveBoolBinop
  , primitiveNumberBinop
  ) where
import Control.Monad.Except
  ( ExceptT
  , runExceptT
  , throwError
  , catchError
  )
import Control.Monad.Trans.State
  ( StateT
  , get
  , modify
  , evalStateT
  , mapStateT
  )
import Control.Monad.Reader
  ( ReaderT
  , runReaderT
  , withReaderT
  , ask
  )
import Control.Monad.Trans.Class( lift )
import Control.Monad.Identity( Identity(runIdentity) )
import Data.IORef( IORef )
 
import qualified Types.Parser as T
import qualified Error as E
import Utils.Assoc( Assoc )
  
type IOExcept = EitherT E.Error IO
type Env = IORef (Vtable -> IOExcept Vtable)
data Vtable = Vtable [(T.Name Value, Vtable -> IOExcept Value)]
type Vtables = Vtable -> Vtable -> IOExcept Vtable
type Eval = State Integer

liftIO :: IO a -> IOExcept a
liftIO = lift

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs++ys)

emptyVtable :: Vtable
emptyVtable = Vtable []

lookupEnv :: T.Name Value -> (Vtable -> IOExcept Vtable) -> Vtable -> IOExcept Value
lookupEnv k f v@(Vtable xs) =
  do{ env <- f v
    ; maybe
        ($ v)
        (throwError $ E.UnboundVar "Unbound var" (show k))
        (k `lookup` xs)
    }
    
lookupVtable :: T.Name Value -> Vtable -> IOExcept Value
lookupVtable k v@(Vtable xs) =
  maybe
    ($ v)
    (throwError $ E.UnboundVar "Unbound var" (show k))
    (k `lookup` xs)

insertVtable :: T.Name Value -> (Vtable -> IOExcept Value) -> Vtable -> IOExcept Vtable
insertVtable k vf (Vtable xs) = return $ Vtable ((k, vf):xs)

emptyVtables :: Vtables
emptyVtables l r = return emptyVtable
    
looksup :: (Vtable -> IOExcept (T.Name Value)) -> Vtables -> Vtable -> IOExcept Value
looksup kf vs v =
  do{ x@(Vtable xs) <- vs emptyVtable emptyVtable
    ; k <- kf v
    ; maybe
        ($ x)
        (throwError $ E.UnboundVar "Unbound var" (show x))
        (k `lookup` xs)
    }
    
concats :: Vtables -> Vtables -> Vtables
concats vs ws l r = concatVtable <$> mv' <*> mw'
  where
    mv' = catchError (ws l r) handleUnboundVar >>= \w -> vs l (w `concatVtable` r)
    mw' = catchError (vs l r) handleUnboundVar >>= \v -> ws (l `concatVtable` v) r  
    
    handleUnboundVar (E.UnboundVar _ _) = return emptyVtable
    handleUnboundVar e = throwError e
    
inserts :: (Vtable -> IOExcept (T.Name Value)) -> (Vtable -> IOExcept Value) -> Vtables
inserts kf vf l r = catchError (do{ k <- kf (l `concatVtable` r); return Vtable [(k, vf)] }) handleUnboundVar
  where
    
runEval :: Eval a -> a
runEval m = evalStateT m 0

data Value = String String | Number Double | Bool Bool | Node Integer Vtables | Symbol Integer | BuiltinSymbol BuiltinSymbol
data BuiltinSymbol = SelfSymbol | ResultSymbol | RhsSymbol | NegSymbol | NotSymbol | AddSymbol | SubSymbol | ProdSymbol | DivSymbol | PowSymbol | AndSymbol | OrSymbol | LtSymbol | GtSymbol | EqSymbol | NeSymbol | LeSymbol | GeSymbol
  deriving (Eq, Ord)
  
instance Show BuiltinSymbol where
  show SelfSymbol = "Self"
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
  
  
newNode :: Eval (Vtables -> Value)
newNode =
  do{ i <- get
    ; modify (+1)
    ; return (Node i)
    }
    
unNode :: Value -> Vtables
unNode (String x) = const (primitiveStringSelf x)
unNode (Number x) = const (primitiveNumberSelf x)
unNode (Bool x) = const (primitiveBoolSelf x)
unNode (Node _ s) = s
unNode (TmpNode s) = s
unNode (Symbol _) = const []
unNode (BuiltinSymbol _) = const []

primitiveStringSelf :: String -> Vtable
primitiveStringSelf x = []

primitiveNumberSelf :: Double -> Vtable
primitiveNumberSelf x = []

primitiveBoolSelf :: Bool -> Vtable
primitiveBoolSelf x = []

newSymbol :: Eval Value
newSymbol =
  do{ i <- get
    ; modify (+1)
    ; return (Symbol i)
    }

selfSymbol :: Value
selfSymbol = BuiltinSymbol SelfSymbol

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
undefinedNumberOp s = throwError . E.PrimitiveOperation $ "Operation " ++ show s ++ " undefined for numbers"

undefinedBoolOp :: Show s => s -> IOExcept a
undefinedBoolOp s = throwError . E.PrimitiveOperation $ "Operation " ++ show s ++ " undefined for booleans"

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
