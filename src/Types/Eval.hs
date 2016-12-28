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
import Control.Applicative( (<|>) )
 
import qualified Types.Parser as T
import qualified Error as E
  
type IOExcept = ExceptT E.Error IO
data Vtable = Vtable [(T.Name Value, IOR Value)]
newtype Super = Super { getSuper :: Vtable }
newtype Self = Self { getSelf :: Vtable }
type ObjR = ReaderT (Super, Self)
type IOR = ObjR IOExcept
newtype CEnv = CEnv { getCEnv :: IOR Vtable }
type ObjF m = ReaderT CEnv (ObjR m)
type IOF = ObjF IOExcept
type Vtables = ReaderT (IOExcept Vtable, IOExcept Vtable) IOExcept (Self, Super)
type Eval = State Integer

liftIO :: IO a -> IOExcept a
liftIO = lift

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs++ys)

emptyVtable :: Vtable
emptyVtable = Vtable []

insertVtable :: T.Name Value -> IOR Value -> Vtable -> IOExcept Vtable
insertVtable k vf (Vtable xs) = return $ Vtable ((k, vf):xs)

deleteVtable :: T.Name Value -> Vtable -> IOExcept Vtable
deleteVtable k (Vtable xs) = return (Vtable $ filter ((/= k) . fst) xs)

mapObjR = mapReaderT
runObjR = runReaderT
askObjR = ask
liftObjR = lift

lookupR :: T.Name Value -> IOR Value
lookupR k =
  do{ (Self (Vtable xs), Super (Vtable xs)) <- ask
    ; maybe
        (throwError $ E.UnboundVar "Unbound var" (show k))
        (>>= id)
        (k `lookup` xs <|> k `lookup` ys)
    }

mapObjF = mapReaderT . mapObjR
runObjF m = runReaderT . runObjR m
askObjF = lift askObjR
liftObjF = lift . liftObjR
    
lookupF :: T.Name Value -> IOF Value
lookupF k = 
  do{ CEnv (Vtable xs) <- ask
    ; maybe
        (throwError $ E.UnboundVar "Unbound var" (show k))
        (lift . (>>= id))
        (k `lookup` xs)
    }

singletonVtables :: Vtable -> Vtables
singletonVtables v = return $ return (Self v, Super emptyVtable)

emptyVtables :: Vtables
emptyVtables = singletonVtables emptyVtable

execVtables :: Vtables -> IOExcept (Self, Super)
execVtables vs = runReader vs (return emptyVtable, return emptyVtable)
  
lookupVtables :: T.Name Value -> Vtables -> IOExcept Value
lookupVtables k vs =
  do{ (self, super) <- execVtables vs
    ; runReaderT (lookupR k) (self, super)
    }
  
lookupValueR :: IOR (T.Name Value) -> IOR Value -> IOR Value
lookupValueR kr vr =
  do{ k <- kr
    ; v <- vr
    ; lift $ lookupVtables k (unNode v)
    }
    
catchUnboundVar :: IOExcept a -> IOExcept a -> IOExcept a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: IOExcept a -> E.Error -> IOExcept a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

concats :: Vtables -> Vtables -> Vtables
concats vs ws = ReaderT $ \ (l, r) ->
  do{ let w' = 
            catchUnboundVar
              (pure emptyVtable)
              (fuse <$> runReaderT ws (l, r))
          v' =
            catchUnboundVar
              (pure emptyVtable)
              (fuse <$> runReaderT vs (l, r))
    ; (self, super) <- runReaderT vs (l, concatVtable <$> w' <*> r)
    ; super' <- fuse <$> runReaderT ws (concatVtable <$> l <*> v', r)
    ; return (self, Super $ getSuper super `concatVtable` super')
    }
    
unpacks :: IOExcept Value -> Vtables -> Vtables
unpacks mv vs =
  do{ (self, super) <- vs
    ; xs <- lift $
        do{ v <- mv
          ; fuse <$> execVtables (unNode v)
          }
    ; let self' = getSelf self `concatVtable` xs
    ; return (Self self', super)
    }

fuse :: (Self, Super) -> Vtable
fuse (Self self, Super super) = self `concatVtable` super
    
inserts :: IOR (T.Name Value) -> IOR Value -> Vtables -> Vtables
inserts kf vf vs =
  do{ (self, super) <- vs
    ; k <- lift $ runReaderT kf (self, super)
    ; self' <- lift $ insertVtable k vf (getSelf self)
    ; return (Self self', super)
    }

deletes :: IOR (T.Name Value) -> Vtables -> Vtables
deletes kf vs =
  do{ (self, super) <- vs
    ; k <- lift $ runReaderT kf (self, super)
    ; self' <- lift $ k `deleteVtable` getSelf self
    ; super' <- lift $ k `deleteVtable` getSuper super
    ; return (Self self', Super super')
    }

runEval :: Eval a -> a
runEval m = evalState m 0

data Value = String String | Number Double | Bool Bool | Node Integer Vtables | Symbol Integer | BuiltinSymbol BuiltinSymbol
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
  
  
newNode :: Eval (Vtables -> Value)
newNode =
  do{ i <- get
    ; modify (+1)
    ; return (Node i)
    }
    
unNode :: Value -> Vtables
unNode (String x) = singletonVtables $ primitiveStringSelf x
unNode (Number x) = singletonVtables $ primitiveNumberSelf x
unNode (Bool x) = singletonVtables $ primitiveBoolSelf x
unNode (Node _ vs) = vs
unNode (Symbol _) = emptyVtables
unNode (BuiltinSymbol _) = emptyVtables

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
