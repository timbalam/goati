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
import Control.Monad.Trans.Class( lift )
import Control.Applicative( (<|>) )
 
import qualified Types.Parser as T
import qualified Error as E
  
type IOExcept = ExceptT E.Error IO
data Vtable = Vtable [(T.Name Value, IOClassed Value)]
newtype Self = Self { getSelf :: Vtable }
newtype Env = Env { getEnv :: IOClassed Vtable }
type Classed = ReaderT Self
type IOClassed = Classed IOExcept
type Scoped = ReaderT Env
type LR m = Reader (m, m)
type Classes = LR (IOExcept Self) (IOExcept Self)
type Scope = Scoped Identity (Env, IOExcept Self)
type Scopes = LR Scope Scope
type Eval = State Integer

liftIO :: IO a -> IOExcept a
liftIO = lift

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

concatVtable :: Vtable -> Vtable -> Vtable
concatVtable (Vtable xs) (Vtable ys) = Vtable (xs++ys)

emptyVtable :: Vtable
emptyVtable = Vtable []

throwUnboundVar :: T.Name Value -> IOClassed a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: IOExcept a -> IOExcept a -> IOExcept a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: IOExcept a -> E.Error -> IOExcept a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err
 
lookupVtable :: T.Name Value -> Vtable -> IOClassed Value
lookupVtable k (Vtable ys) = 
  maybe
    (throwUnboundVar k)
    id
    (k `lookup` ys)

insertVtable :: T.Name Value -> IOClassed Value -> Vtable -> Vtable
insertVtable k vr (Vtable xs) = Vtable ((k, vr):xs)

deleteVtable :: T.Name Value -> Vtable -> Vtable
deleteVtable k = insertVtable k (throwUnboundVar k)

mapVtable :: (T.Name Value -> IOClassed Value -> IOClassed Value) -> Vtable -> Vtable
mapVtable f (Vtable xs) = Vtable $ map (\ (k, vf) -> (k, f k vf)) xs

showVtable :: Vtable -> String
showVtable (Vtable xs) = show (map fst xs)

bindClassed :: Monad m => Classed m Vtable -> Classed m Vtable
bindClassed vr =
  do{ v <- vr
    ; self <- askClassed
    ; return $ mapVtable (const $ local (const self) ) v
    }

mapClassed = mapReaderT
runClassed = runReaderT

askClassed :: Monad m => Classed m Self
askClassed = ask

liftClassed :: Monad m => m a -> Classed m a
liftClassed = lift

lookupSelf :: T.Name Value -> IOClassed Value
lookupSelf k =
  do{ Self self <- askClassed
    ; lookupVtable k self
    }
   
mapScoped = mapReaderT   
runScoped = runReaderT

askScoped :: Monad m => Scoped m Env
askScoped = ask

liftScoped :: Monad m => m a -> Scoped m a
liftScoped = lift
    
lookupEnv :: T.Name Value -> Scoped IOClassed Value
lookupEnv k =
  do{ Env env <- askScoped
    ; liftScoped $ (lookupVtable k <$> env)
    }

execClasses :: Classes -> IOExcept Self
execClasses vs = runReader vs (empty, empty)
  where
    empty = return $ Self emptyVtable
  
lookupClasses :: T.Name Value -> Classes -> IOExcept Value
lookupClasses k vs =
  do{ t <- execClasses vs
    ; runClassed (lookupSelf k) t
    }
  
lookupValue :: IOClassed (T.Name Value) -> IOClassed Value -> IOClassed Value
lookupValue kr vr =
  do{ k <- kr
    ; v <- vr
    ; liftClassed $ lookupClasses k (unNode v) 
    }

liftSelf2 f (Self a) (Self b) = Self $ a `f` b
concatSelf = liftSelf2 concatVtable

concats :: Classes -> Classes -> Classes
concats vc wc = Reader $ \ (l, r) -> 
  concatSelf <$> v <*> w
    where
      w' = runReader (OrEmpty <$> wc) (l, r)
      v' = runReader (OrEmpty <$> vc) (l, r)
      v = runReader vc (l, concatSelf <$> w' <*> r)
      w = runReader wc (concatSelf <$> l <*> v', r)
      OrEmpty m = catchUnboundVar m (pure $ Self emptyVtable)
      
      
concatScope :: Scope -> Scope -> Scope
concatScope vf wf =
  do{ (ve, vs) <- vf
    ; (we, ws) <- wf
    ; return (ve `concatEnv` we, vs `concatSelf` ws)
    }
      
concatsScopes :: Scopes -> Scopes -> Scopes
concatsScopes vs ws = Reader $ \ (lf, rf) ->
  vf `concatScope` wf
    where
      wf' = OrEmpty <$> (runReader vs (lf, lr))
      vf' = OrEmpty <$> (runReader ws (lf, lr))
      vf = runReader vs (lf, wf' `concatScope` rf)
      wf = runReader ws (lf `concatScope` vf', rf)
      OrEmpty (e, s) = (OrEmptyEnv e, OrEmptySelf s)
      OrEmptyEnv (Env env) = Env $ mapClassed (\ m -> catchUnboundVar m (pure emptyVtable)) env
      OrEmptySelf m = catchUnboundVar m (pure . Self $ emptyVtable)
     
unpacks :: IOExcept Value -> Classes
unpacks mv = return $
  do{ v <- mv
    ; vself <- execClasses (unNode v)
    ; runClassed (bindClassed askClassed) vself
    }
    
liftEnv2 f (Env a) (Env b) = Env $ f <$> a <*> b
concatEnv = liftEnv2 concatVtable
    
insertsSelf :: Scoped IOClassed (T.Name Value) -> Scoped IOClassed Value -> Scopes
insertsSelf kf vf = Reader $ \ (lf, rf) ->
  do{ (env, self) <- lf `concatScope` rf
    ; self' <- mapScoped (\ vr ->
        do{ k <- runClassed . runScoped kf $ env self
          ; return . Self $ insertVtable k vr emptyVtable
          }) vf
    ; return (Env . return $ emptyVtable, self')
    }
    
insertsEnv :: Scoped IOClassed (T.Name Value) -> Scoped IOClassed Value -> Scopes
insertsEnv kf vf = Reader $ \ (lf, rf) ->
  do{ (env, self) <- lf `concatScope` rf
    ; env' <- mapScoped (\ vr ->
        do{ k <- runClassed . runScoped kf $ env self
          ; Env . return $ insertVtable k vr emptyVtable
          }) vf
    ; return (env', return . Self $ emptyVtable)
    }     

deletes :: Scoped IOClassed (T.Name Value) -> Scopes
deletes kf = Reader $ \ (lf, rf) ->
  do{ (env, self) <- lf `concatScope` rf
    ; mapScoped (\ vr ->
        do{ k <- runClassed . runScoped kf $ env self
          ; let v = deleteVtable k emptyVtable
          ; (Env . return $ v, return . Self $ v)
          }
    }

runValue :: Scoped IOClassed Value -> IOExcept Value
runValue vf = runClassed . runScoped vf $ (Env $ return primitiveBindings) (Self emptyVtable)

runValue_ :: Scoped IOClassed Value -> IOExcept ()
runValue_ vf = runValue vf >> return ()
    
runEval :: Eval a -> a
runEval m = evalState m 0

data Value = String String | Number Double | Bool Bool | Node Integer Classes | Symbol Integer | BuiltinSymbol BuiltinSymbol
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
  
  
newNode :: Eval (Classes -> Value)
newNode =
  do{ i <- get
    ; modify' (+1)
    ; return (Node i)
    }
    
unNode :: Value -> Classes
unNode (String x) = liftLR . return $ primitiveStringSelf x
unNode (Number x) = liftLR . return $ primitiveNumberSelf x
unNode (Bool x) = liftLR . return $ primitiveBoolSelf x
unNode (Node _ vs) = vs
unNode (Symbol _) = liftLR . return $ Self emptyVtable
unNode (BuiltinSymbol _) = liftLR . return $ Self emptyVtable

primitiveStringSelf :: String -> Self
primitiveStringSelf x = Self emptyVtable

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = Self emptyVtable

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = Self emptyVtable

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

primitiveBindings :: Env
primitiveBindings = emptyVtable

