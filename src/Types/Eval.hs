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
  , execStateT
  , mapStateT
  , get
  , put
  , modify'
  , State
  , evalState
  , mapState
  , runState
  , state
  )
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader
  ( ReaderT(ReaderT)
  , runReaderT
  , mapReaderT
  , withReaderT
  , Reader
  , runReader
  , mapReader
  , withReader
  )
import Control.Monad.Trans.Class
import Control.Applicative
  ( (<|>)
  , liftA2
  )
import List.Transformer
  ( ListT(..)
  , Step(..)
  )
import Control.Monad.Trans.Free
  ( FreeF(..)
  , FreeT(..)
  , liftF
  , iterTM
  , transFreeT
  , retractT
  , hoistFreeT
  , MonadFree
  , wrap
  )
import Data.Functor.Identity
import Data.Maybe
  ( isJust
  , mapMaybe
  , catMaybes
  )
import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  

-- IOExcept
type IOExcept = ExceptT E.Error IO

runIOExcept :: IOExcept a -> (E.Error -> IO a) -> IO a
runIOExcept m catch = runExceptT m >>= either catch return

throwUnboundVar :: (Show k, MonadError E.Error m) => k -> m a
throwUnboundVar k = throwError $ E.UnboundVar "Unbound var" (show k)

catchUnboundVar :: MonadError E.Error m => m a -> m a -> m a
catchUnboundVar v a = catchError v (handleUnboundVar a)

handleUnboundVar :: MonadError E.Error m => m a -> E.Error -> m a
handleUnboundVar a (E.UnboundVar _ _) = a
handleUnboundVar _ err = throwError err

deletes :: (Show k, MonadError E.Error m) => k -> m Value -> m Value
deletes k  = const (throwUnboundVar k)


-- Vtable
type Vtable k r = M.Map k (IOClasses r Value)
type DiffList k r = [(k, IOClasses r Value -> IOClasses r Value)]
type RefTable r = Vtable T.Ident r
type ObjTable r = Vtable (T.Name Value) r

emptyVtable :: Vtable k r
emptyVtable = M.empty

concatVtable :: Ord k => Vtable k r -> Vtable k r -> Vtable k r
concatVtable = M.union

lookupVtable :: (Ord k, Show k) => k -> Vtable k r -> IOClasses r Value
lookupVtable k = M.findWithDefault (throwUnboundVar k) k

insertVtable :: Ord k => k -> IOClasses r Value -> Vtable k r -> Vtable k r
insertVtable = M.insert

alterVtable :: (Ord k, Show k) => (IOClasses r Value -> IOClasses r Value) -> k -> Vtable k r -> Vtable k r
alterVtable f k = M.alter f' k
  where
    f' = Just . f . maybe (throwUnboundVar k) id

deleteVtable :: Ord k => k -> Vtable k r -> Vtable k r
deleteVtable k = M.delete k

withVtable :: (r' -> r) -> Vtable k r -> Vtable k r'
withVtable = M.map . withClasses

showVtable :: Show k => Vtable k r -> String
showVtable = show . M.keys

fromDiffList :: (Ord k, Show k) => DiffList k r -> Vtable k r
fromDiffList = M.mapWithKey (\ k f -> f (throwUnboundVar k)) . M.fromListWith (flip (.))

toDiffList :: Vtable k r -> DiffList k r
toDiffList = M.toList . M.map const

-- Classed 
type Classed = ReaderT
type IOClassed r = ReaderT r IOExcept

mapClassed :: (m a -> n b) -> Classed r m a -> Classed r n b
mapClassed = mapReaderT

withClassed :: (r' -> r) -> Classed r m a -> (Classed r' m a)
withClassed = withReaderT

runClassed :: Monad m => Classed r m a -> r -> m a
runClassed = runReaderT

-- Classes
type Classes r = FreeT (Reader r) 
type IOClasses r = FreeT (Reader r) IOExcept

mapClasses :: Monad m => (forall a. m a -> n a) -> Classes r m b -> Classes r n b
mapClasses = hoistFreeT

withClasses :: Monad m => (r' -> r) -> Classes r m a -> Classes r' m a
withClasses f = transFreeT (withReader f)

retractClasses :: Monad m => Classes r m a -> Classed r m a
retractClasses = retractT . transFreeT ftotm
  where
    ftotm :: Monad m => Classed r Identity a -> Classed r m a
    ftotm = mapClassed (return . runIdentity)
    
runClasses :: Monad m => Classes r m a -> r -> m a
runClasses  = runClassed . retractClasses

mergeFreeT :: (Monad m, Applicative f) => FreeT f m (a -> b) -> FreeT f m a -> FreeT f m b
mergeFreeT lift f = goT 
  where 
    goT (FreeT ma) (FreeT mb) = FreeT (liftA2 goF ma mb)
    
    goF (Free fa) (Free fb) = Free (liftA2 goT fa fb)
    goF (Free fa) (Pure b) = Free (liftA2 goT fa (pure (return b)))
    goF (Pure a) (Free fb) = Free (liftA2 goT (pure (return a)) fb)
    goF (Pure a) (Pure b) = Pure (f b)
    
zipClasses :: Monad m => Classes r m (a -> b) -> Classes r m a -> Classes r m  b
zipClasses = mergeFreeT

liftClasses2 :: Monad m => (a -> b -> c) -> Classes r m a -> Classes r m b -> Classes r m c
liftClasses2 f ar br = (f <$> ar) `zipClasses` br

liftClassed :: Monad m => Classed r m a -> Classes r m a
liftClassed = wrap . fmap lift . tmtofm
  where
    tmtofm :: Classed r m a -> Classed r Identity (m a)
    tmtofm = mapClassed Identity

askClasses :: Monad m => Classes r m r
askClasses = liftF ask

asksClasses :: Monad m => (r -> a) -> Classes r m a
asksClasses f = liftF (asks f)

lookupClassesWith :: (Ord k, Show k) => k -> (r -> Vtable k r) -> IOClasses r Value
lookupClassesWith k f = asksClasses f >>= lookupVtable k

lookupClassesWithM :: (Ord k, Show k) => k -> (r -> IOClasses r (Vtable k r)) -> IOClasses r Value
lookupClassesWithM k f = askClasses >>= f >>= lookupVtable k

-- Self
data Self = Self { unSelf :: ObjTable Self }

emptySelf = Self emptyVtable

-- Scope
data Scope = Scope { penv :: RefTable Scope, cenv :: RefTable Scope, cobj :: ObjTable Scope, self :: ObjTable Scope }

lookupEnv :: T.Ident -> IOClasses Scope Value
lookupEnv k = lookupCenv `catchUnboundVar` (lookupCur `catchUnboundVar` lookupPenv)
  where
    lookupCenv = lookupClassesWith k cenv
    lookupCur = lookupClassesWith (T.Ref k) cobj
    lookupPenv = lookupClassesWith k penv

lookupSelf :: T.Name Value -> IOClasses Scope Value
lookupSelf k = lookupClassesWith k self
    
-- Eval
type Eval = State Integer

mapEval = mapState
runEval m = evalState m 0

-- Node
type NodeList r m = FreeT (State r) m ()
type IONodeList r = FreeT (State r) IOExcept ()
   
    
toNodeList :: Monad m => Classes r m (r -> r) -> NodeList r m
toNodeList mf = 
  do{ f <- transFreeT (\ r -> state (\ s -> (runReader r s, s))) mf
    ; liftF (state (\ s -> ((), f s)))
    }
    
newtype Comp r a = Comp { toState :: State r a }
instance Functor (Comp r) where
  Comp a `fmap` Comp b = Comp (a `fmap` b)
instance Monoid r => Applicative (Comp r) where
  pure a = Comp (state (\ s -> (a, mempty)))
  Comp sa <*> Comp sb = Comp (state (\s -> let (a, s') = runState sa s; (b, s'') = runState sb s in (a b, s' `mappend` s'')))

mergeNodeList :: (Monoid r, Monad m) => NodeList r m -> NodeList r m -> NodeList r m
mergeNodeList = mergeFreeTWith concatState const
  where
    concatState f s t = state (\ r -> let (a, r') = runState s r; (b, r'') = runState t r in (f a b, r' `mappend` r'')) 

execScope :: Monad m => NodeList Scope m -> Scope -> NodeList Self m
execScope node scope = goT (scope { cenv = emptyVtable, cobj = emptyVtable }) node
  where
    goT :: Monad m => Scope -> NodeList Scope m -> NodeList Self m
    goT scope node = FreeT (do{ nodeF <- runFreeT node; return (goF scope nodeF) })
    
    goF :: Monad m => Scope -> FreeF (State Scope) () (NodeList Scope m) -> FreeF (State Self) () (NodeList Self m)
    goF scope (Free s) = Free s'
      where
        s' = state (\ r -> let (a, scope') = runState s (setSelf scope r); r' = Self (withVtable (setSelf scope') (cobj scope')) in (goT scope' a, r'))
    goF scope (Pure a) = Pure a
    
    setSelf :: Scope -> Self -> Scope
    setSelf scope (Self xs) = scope { self = withVtable forgetScope xs }
    
    forgetScope :: Scope -> Self
    forgetScope scope = Self (withVtable (setSelf scope) (self scope))
        
        
  
execNode :: Monad m => NodeList Self m -> m Self
execNode node = execStateT (retractT (transFreeT ftotm node)) emptySelf
  where
    ftotm = mapStateT (return . runIdentity)
    
execNode' node = goT emptySelf
  where
    goT :: Monad m => Self -> NodeList Self m -> m Self
    goT self node = (do{ f <- runFreeT node; goF self f })
    
    goF :: Monad m => Self -> FreeF (State Self) () (NodeList Self m) -> m Self
    goF self (Free s) = let (a, self') = runState s self in goT self' a
    goF self _ = return self

instance Monoid Self where
  mempty = Self emptyVtable
  Self a `mappend` Self b = Self (a `concatVtable` b)
  
  
type Node = IONodeList Self
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
    f (Symbol _) = fromSelf $ emptySelf
    f (BuiltinSymbol _) = fromSelf $ emptySelf
    fromSelf r = liftF (state (\ _ -> ((), r)))

primitiveStringSelf :: String -> Self
primitiveStringSelf x = emptySelf

primitiveNumberSelf :: Double -> Self
primitiveNumberSelf x = emptySelf

primitiveBoolSelf :: Bool -> Self
primitiveBoolSelf x = emptySelf

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

primitiveBindings :: Vtable k r
primitiveBindings = emptyVtable

