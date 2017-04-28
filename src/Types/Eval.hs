{-# LANGUAGE FlexibleContexts, Rank2Types, GeneralizedNewtypeDeriving, DeriveTraversable #-}

module Types.Eval
  where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding (Endo(Endo), appEndo)
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
import Data.Semigroup ( Max(Max) )
import Data.List ( NonEmpty(NonEmpty), head, tail )
--import Data.Traversable( traverse )
import qualified Data.Map as M
import qualified Data.Map.Merge as M
--import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
  

-- Error
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


-- Tables
newtype Deferred m a = Deferred (WriterT (Max Word) m a) deriving (Functor, Applicative, Foldable, Traversable, Monad, MonadTrans, MonadIO, MonadError e)

runDeferred :: Monad m => Deferred m a -> m ()
runDeferred (Deferred w) = runWriterT w >> return ()


newtype Table k v = Table (M.Map k v)
newtype Tables k v = Tables [Table k v]

emptyTable :: Table k v
emptyTable = Table M.empty

lookupTable :: Ord k => k -> Table k v -> Maybe v
lookupTable k (Table x) = M.lookup k x

insertTable :: (Show k, Ord k) => k -> v -> Table k v -> Table k v
insertTable k v (Table x) = Table (M.insert k v x)

alterFTable :: (Ord k, Functor f) => (Maybe v -> f (Maybe v)) -> k -> Table k v -> f (Table k v)
alterFTable f k (Table x) = Table <$> M.alterF f k x

deleteTable :: Ord k => k -> Table k v -> Table k v
deleteTable k (Table x) = Table (M.delete k x)

showTable :: Show k => Table k v -> String
showTable (Table x) = show (M.keys x)

instance Show k => Show (Table k v) where show = showTable

emptyTables :: Tables k v
emptyTables = Tables []

lookupTables :: (Ord k, Monad m) => k -> Tables k (Deferred m v) -> Maybe (Deferred m v)
-- M.lookup :: k -> Map k v -> Maybe v
lookupTables k (Tables xs) = getAlt (foldMap f (zip (iterate succ mempty) xs))
  where
    f (i, x) = Alt (do{ Deferred w <- lookupTable k x; return (Deferred (tell i >> w)) })

liftTable :: Functor m => (Table k v -> m (Table k v)) -> Tables k v -> m (Tables k v)
liftTable f (Tables []) = Tables <$> f emptyTable
liftTable f (Tables x:xs) = Table <$> ((:xs) <$> (f x)) 

insertTables :: Ord k => k -> v -> Tables k v -> Tables k v
-- M.insert :: k -> v -> Map k v -> Map k v
insertTables k v = runIdentity . liftTable (Identity . insertTable k v)

deferTables :: MonadError E.Error m => Deferred m (Tables k v -> m (Tables k v)) -> Tables k v -> m (Tables k v)
-- M.insert :: k -> v -> Map k v -> Map k v
deferTables (Deferred w) (Tables xs) =
  do{ (f, i) <- runWriterT w
    ; let
        go i [] = go i [emptyTable]
        go i xs@(z:zs)
          | i==minBound = f xs
          | otherwise = (z:) <$> go (pred i) zs
    ; go i xs
    }
    
deferTable :: MonadError E.Error m => Deferred m (Table k v -> m (Table k v)) -> Tables k v -> m (Tables k v)
deferTable = deferTables . fmap liftTable
    
alterFTables :: (Ord k, Functor f) => (Maybe v -> f (Maybe v)) -> k -> Tables k v -> f (Tables k v)
alterFTables f k t =
  maybe
    (return (deleteTables k t))
    (\ v -> return (insertTables k v t))
    <$> f (lookupTables k t)
    
deleteTables :: (Ord k, MonadError E.Error m) => k -> Tables k v -> Tables k v
deleteTables k = insertTables k (throwUnboundVar k)

showTables :: Show k => Tables k v -> String
showTables (Tables xs) = foldMap (\ (i, x) -> show i++":"++show x) (zip (iterate (+1) 1) xs)

instance Show k => Show (Tables k v) where show = showTables


-- Scope
type XT = ExceptT E.Error
type XIO = XT IO
type Self = Tables (T.Name Value) (DX Value)
type Env = Table T.Ident (DX Value)
type DT = Deferred
type DX = Deferred XIO
type X = XT Identity
type ERT = ReaderT Env
type SRT = ReaderT Self
type ESRT m = ERT (SRT m)
type ESR = ESRT Identity

liftToESRT :: Monad m => m a -> ESRT m a
liftToESRT = lift . lift

mapESRT :: (m a -> n b) -> ESRT m a -> ESRT n b
mapESRT = mapReaderT . mapReaderT

liftToXT :: Monad m => m a -> XT m a
liftToXT = lift

runESRT :: ESRT m a -> m a
runESRT m = runReaderT (runReaderT m primitiveBindings) emptyTables

lookupSelf :: T.Name Value -> ESRT DX Value
lookupSelf k =
  do{ self <- lift ask
    ; maybe (throwUnboundVar k) liftToESRT (lookupTables k self)
    } 

lookupEnv :: T.Ident -> ESRT DX Value
lookupEnv k =
  do{ env <- ask
    ; maybe (throwUnboundVar k) liftToESRT (lookupTable k env)
    }

lookupValue :: T.Name Value -> Value -> DX Value
lookupValue k v =
  do{ self <- lift (configureSelf (unNode v))
    ; maybe (throwUnboundVar k) id (lookupTables k self)
    }
    

-- EndoM
newtype EndoM m a = EndoM { appEndoM :: a -> m a }

instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM return
  EndoM f `mappend` EndoM g = EndoM (f <=< g)
  
type Endo = EndoM Identity

endo :: (a -> a) -> Endo a
endo f = EndoM (Identity . f)

appEndo :: Endo a -> (a -> a)
appEndo (EndoM f) = runIdentity . f

-- ScopeBuilder
type NodeS v = Table (T.Name Value) (ValS v)
data ValS v = ValS Id (NodeS v) | ValP v
type EnvS v = Table T.Ident (DX (ValS v))
type SelfS v = Tables (T.Name Value) (DX (ValS v))
type EnvB = EnvS (DX Value)
type SelfB = SelfS (DX Value)
type SelfD = SelfS (DX Value -> (Endo EnvB, EndoM XIO SelfB))
type ScopeB = Env -> Self -> (Endo EnvB, EndoM XIO SelfB)

emptyBuilder :: NodeS v
emptyBuilder = emptyTable

newValB :: MonadState Ids m => m (NodeS v -> ValS v)
newValB = useId NodeB


deconsVal :: Monoid m => ValS (DX Value -> m) -> DX Value -> m
deconsVal (ValP f) mv = f mv
deconsVal (ValS _ (Table x)) mv = M.foldMap go x
  where
    go k b = deconsVal b (mv >>= lookupValue k)
    
    
deconsSelf :: Monoid m => SelfS (DX Value -> m) -> DX Value -> m
deconsSelf (Tables xs) mv = foldMap (\ (Table x) -> M.foldMapWithKey go x) xs
  where
    go k b = deconsVal b (mv >>= lookupValue k)

    
buildVal :: ValS (DX Value) -> Maybe (DX Value) -> DX Value
buildVal (ValP mv) _ = mv
buildVal (ValS i b) mb =
  do{ c <- maybe (return mempty) (fmap unNode) mb
    ; return (Node i (EndoM (return . buildNode b) <> c))
    }
    
buildNode :: NodeS (DX Value) -> Self -> Self
buildNode x self = foldrWithKey go self x
  where
    go :: T.Name Value -> ValS (DX Value) -> Self -> Self
    go k b = alterTables (Just . buildVal b) k
    
    
buildSelf :: SelfB -> Self -> Self
buildSelf (Tables xs) self = foldr (\ x self -> foldrWithKey go self x) self xs
  where
    go :: T.Name Value -> DX (ValS (DX Value) -> Self -> Self
    go k m = alterTables (\ mb -> Just (do{ b <- m; buildVal b mb })) k
    
buildEnv :: EnvB -> Env -> Env
buildEnv x env = foldrWithKey go env x
  where
    go :: T.Ident -> DX (ValS (DX Value)) -> Env -> Env
    go k m = alterTable (\ mb -> Just (do{ b <- m; buildVal b mb })) k

    
insertValS :: MonadError E.Error m => Ided (T.Name Value -> v -> Maybe (ValB v) -> m (ValB v))
insertValS =
  do{ alter <- alterValS
    ; return (\ k v -> alter k (maybe (return (ValP v)) (throwOverlappingDefinitions k)))
    }

deleteValS :: MonadError E.Error m, MonadError E.Error n => Ided (T.Name Value -> Maybe (ValS (n v)) -> m ValS (n v))
deleteValB =
  do{ insert <- insertValS
    ; return (\ k -> insert k (throwUnboundVar k))
    }

alterValS :: MonadError E.Error m => Ided (T.Name Value -> (Maybe (ValS v) -> m (ValS v)) -> Maybe (ValS v) -> m (ValS v))
alterValS = 
  do{ nn <- newNodeB
    ; let
        go k f Nothing =
          do{ v <- f Nothing
            ; return (nn (insertTable k v emptyBuilder))
            }
        go k f (Just (ValP _)) = throwOverlappingDefinitions k
        go k f (Just (ValS _ b)) = nn <$> alterTable (fmap Just . f) b
    ; return go
    } 
    
insertEnvS :: MonadError E.Error m => T.Ident -> v -> EnvS v -> m (EnvS v)
insertEnvS k mv x = insertTableUnique k (return (ValP mv)) x

deleteEnvS :: MonadError E.Error m, MonadError E.Error n => T.Ident -> EnvS (n v)-> m (EnvS (n v))
deleteEnvS k = insertEnvS k (throwUnboundVar k)

alterEnvB :: MonadError E.Error m => T.Ident -> DX (Maybe (ValS v) -> X (ValS v)) -> EnvS v -> m (EnvS v)
alterEnvB k mf = runIdentity . alterFTable (\ mb -> Identity (Just (do{ f <- mf; lift (nn <$> f mb) }))) k

insertSelfS :: MonadError E.Error m => T.Name Value -> v -> SelfS v -> m (SelfS v)
insertSelfS k v = alterFTable (maybe (return (ValP v)) (throwOverlappingDefinitions k)) k

deleteSelfS :: MonadError E.Error m, MonadError E.Error n => T.Name Value -> SelfS (n v) -> m (SelfS (n v))
deleteSelfS k = insertSelfS k (throwUnboundVar k)

alterSelfS :: T.Name Value -> DX (Maybe (ValS v) -> X (ValS v)) -> SelfS v -> SelfS v
alterSelfS k mf t = alterTables (\ mb -> Just (do{ f <- mf; lift (nn <$> f (lookupTables k xs)) }) k t


type Scope = Endo (Env -> ESRT (WriterT (EndoM XIO Self) XIO) Env)
type Classed = Endo (Self -> SRT XIO Self)

initial :: Monad m => a -> Endo m a
initial a = Endo (const (return a))

configure :: Monad m => (super -> m self) -> Endo (ReaderT self m) super -> m self
configure g (Endo f) = mfix (runReaderT (mfix f >>= lift g))

buildScope :: ScopeB -> Ided Scope
buildScope scopeBuilder =
  Endo (\ env -> 
    do{ (Endo f, Endo g) <- scopeBuilder <$> ask <*> lift ask
      ; tell (return . buildSelf (g emptyBuilder))
      ; lift (lift (f env))
      })
      
scope :: ESR (EndoM XIO EnvB, EndoM XT SelfB) -> ScopeB
scope m = runReaderT . runReaderT m

configureScope :: Scope -> Classed
configureScope scope =
  EndoM (\ self ->
    -- configure buildEnv scope :: SRT (WriterT (EndoM XIO Scope) XIO) Env
    do{ Endo f <- mapReaderT execWriterT (configure buildEnv scope)
      ; return (f self)
      })


-- Ided
newtype Id = Id { getId :: Integer } deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
newtype Ided a = Ided (State Ids a) deriving (Functor, Applicative, Monad, MonadState Ids)

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))

runIded :: Ided a -> a    
runIded (Ided m) = evalState m (Id `fmap` iterate (+1) 0)

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
    fromSelf = initialSelf

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

primitiveBindings :: Table k v
primitiveBindings = emptyTable

