module Types.Eval
  ( IOExcept
  , runIOExcept
  , catchUnboundVar
  , liftIO
  , Vtable(Vtable)
  , concatVtable
  , emptyVtable
  , insertVtable
  , deleteVtable
  , lookupVtable
  , EnvF
  , emptyEnvF
  , concatEnvF
  , lookupEnvF
  , execEnvF
  , EnvR
  , ValueF
  , KeyF
  , lookupValueF
  , Vtables
  , execVtables
  , emptyVtables
  , inserts
  , concats
  , deletes
  , Eval
  , runEval
  , Value(String, Number, Bool)
  , newNode
  , unNode
  , newSymbol
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
  ( State
  , get
  , modify
  , evalState
  )
import Control.Monad.Reader
  ( ReaderT
  , runReaderT
  , withReaderT
  , ask
  )
import Control.Monad.Trans.Class( lift )
import Control.Monad.Identity( Identity(runIdentity) )
 
import qualified Types.Parser as T
import qualified Error as E
--import Utils.Assoc( Assoc )
  
type IOExcept = ExceptT E.Error IO
type EnvF = Vtable -> Vtable -> IOExcept Vtable
type ValueF = Vtable -> Vtable -> IOExcept Value
type KeyF = Vtable -> Vtable -> IOExcept (T.Name Value)
data Vtable = Vtable [(T.Name Value, ValueF)]
type Vtables = IOExcept Vtable -> IOExcept Vtable -> IOExcept Vtable
type Vtables' = IOExcept Vtable -> IOExcept Vtable -> IOExcept (Vtable, Vtable)
type Eval = State Integer

liftIO :: IO a -> IOExcept a
liftIO = lift

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs++ys)

emptyVtable :: Vtable
emptyVtable = Vtable []

insertVtable :: T.Name Value -> ValueF -> Vtable -> IOExcept Vtable
insertVtable k vf (Vtable xs) = return $ Vtable ((k, vf):xs)

deleteVtable :: T.Name Value -> Vtable -> IOExcept Vtable
deleteVtable k (Vtable xs) = return (Vtable $ filter ((/= k) . fst) xs)

lookupVtable :: T.Name Value -> ValueF
lookupVtable k v@(Vtable xs) s@(Vtables ys) =
  maybe
    (throwError $ E.UnboundVar "Unbound var" (show k))
    (\f -> f v s)
    (k `lookup` xs <|> k `lookup` ys)
    
concatEnvF :: EnvF -> EnvF -> EnvF
concatEnvF x y v s = concatVtable <$> x v s <*> y v s

emptyEnvF :: EnvF
emptyEnvF _ _ = return emptyVtable

lookupEnvF :: T.Name Value -> EnvF -> ValueF
lookupEnvF k e v s =
  do{ Vtable xs <- e v s
    ; maybe
        (throwError $ E.UnboundVar "Unbound var" (show k))
        (\f -> f v s)
        (k `lookup` xs)
    }
  
execEnvF :: EnvF -> EnvF -> Vtable -> Vtable -> EnvF
execEnvF ne e v s = ne `concatEnvF` e'
  where
    e' _ _ = e v s
  

singletonVtables :: Vtable -> Vtables
singletonVtables v _ _ = return v

singletonVtables' :: Vtable -> Vtables'
singletonVtables' v _ _ = return (v, emptyVtable)

emptyVtables :: Vtables
emptyVtables = singletonVtables emptyVtable

emptyVtables' :: Vtables'
emptyVtables' = singletonVtables' emptyVtable

execVtables :: Vtables  -> IOExcept Vtable
execVtables vs = vs (return emptyVtable) (return emptyVtable)

execVtables' :: Vtables' -> IOExcept (Vtable, Vtable)
execVtables' vs = vs (return emptyVtable) (return emptyVtable)
    
lookupValueF :: KeyF -> ValueF -> ValueF
lookupValueF kf vf v s =
  do{ k <- kf v s
    ; val <- vf v s
    ; (x, s') <- execVtables (unNode val)
    ; (k `lookupVtable`) x s'
    }
    
catchUnboundVar :: IOExcept a -> IOExcept a -> IOExcept a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: IOExcept a -> E.Error -> IOExcept a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

concats :: Vtables -> Vtables -> Vtables
concats vs ws l r = concatVtable <$> v <*> w
  where
    v = vs l (concatVtable <$> catchUnboundVar (pure emptyVtable) (ws l r) <*> r)
    w = ws (concatVtable <$> l <*> catchUnboundVar (pure emptyVtable) (vs l r)) r
    
fuse' :: Vtables' -> Vtables
fuse' ws l r = (uncurry concatVtable) <$> ws l r
    
concats' :: Vtables' -> Vtables' -> Vtables'
concats' vs ws l r =
  do{ (l, r) <- vs l (concatVtable <$> catchUnboundVar (pure emptyVtable) (fuse' ws l r) <*> r)
    ; let w = fuse' ws (concatVtable <$> l <*> catchUnboundVar (pure emptyVtable) (fuse' vs l r)) r
    ; (,) l <$> (concatVtable r <$> w) 
    }
    
inserts' :: KeyF -> ValueF -> Vtables' -> Vtables'
inserts kf vf vs l r =
  do{ (v, s) <- vs l r
    ; k <- kf v s
    ; return $ (Vtable [(k, vf)] `concatVtable` v, s)
    }

deletes :: KeyF -> Vtables' -> Vtables'
deletes kf vs l r =
  do{ (v, s) <- vs l r
    ; k <- kf v s
    ; (,) <$> k `deleteVtable` v <*> k `deleteVtable` s
    }

runEval :: Eval a -> a
runEval m = evalState m 0

data Value = String String | Number Double | Bool Bool | Node Integer Vtables' | Symbol Integer | BuiltinSymbol BuiltinSymbol
data BuiltinSymbol = SelfSymbol | ResultSymbol | RhsSymbol | NegSymbol | NotSymbol | AddSymbol | SubSymbol | ProdSymbol | DivSymbol | PowSymbol | AndSymbol | OrSymbol | LtSymbol | GtSymbol | EqSymbol | NeSymbol | LeSymbol | GeSymbol
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
  
  
newNode :: Eval (Vtables -> Vtables -> Value)
newNode =
  do{ i <- get
    ; modify (+1)
    ; return (Node i)
    }
    
unNode :: Value -> (Vtables, Vtables)
unNode (String x) = (singletonVtables $ primitiveStringSelf x, emptyVtables)
unNode (Number x) = (singletonVtables $ primitiveNumberSelf x, emptyVtables)
unNode (Bool x) = (singletonVtables $ primitiveBoolSelf x, emptyVtables)
unNode (Node _ v s) = (v, s)
unNode (Symbol _) = (emptyVtables, emptyVtables)
unNode (BuiltinSymbol _) = (emptyVtables, emptyVtables)

primitiveStringSelf :: String -> Vtable
primitiveStringSelf x = emptyVtable

primitiveNumberSelf :: Double -> Vtable
primitiveNumberSelf x = emptyVtable

primitiveBoolSelf :: Bool -> Vtable
primitiveBoolSelf x = emptyVtable

newSymbol :: Eval Value
newSymbol =
  do{ i <- get
    ; modify (+1)
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
