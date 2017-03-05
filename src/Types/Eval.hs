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
  , State
  , evalState
  , mapState
  )
import Control.Monad.IO.Class
import Control.Monad.Reader.Class
import Control.Monad.Trans.Reader
  ( ReaderT(ReaderT)
  , runReaderT
  , mapReaderT
  , Reader
  , runReader
  , mapReader
  )
import Control.Monad.Trans.Class
import Control.Applicative( (<|>) )
import List.Transformer
  ( ListT(..)
  , Step(..)
  )
import Control.Monad.Trans.Free
  ( FreeF(..)
  , FreeT(..)
  , liftF
  , transFreeT
  , retractT
  , hoistFreeT
  , MonadFree
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
type RefTable = Rtable T.Ident
type ObjTable = Rtable (T.Name Value)

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
deleteVtable k = M.delete

withVtable :: (r' -> r) -> Vtable k r -> Vtable k r'
withVtable = M.map . withClasses

showVtable :: Show k => Vtable k r -> String
showVtable a = show . M.keys

fromDiffList :: (Ord k, Show k) => DiffList k r -> Vtable k r
fromDiffList = M.mapWithKey (\ k f -> f (throwUnboundVar k)) . M.fromListWith (flip (.))

toDiffList :: Vtable k r -> DiffList k r
toDiffList a = M.toList . M.map const

-- Classed 
type Classed = ReaderT
type IOClassed r = ReaderT r IOExcept

mapClassed :: (m a -> n b) -> Classed r m a -> Classed r n b
mapClassed = mapReaderT

withClassed :: (r' -> r) -> Classed r m a -> (Classed r' m a)

runClassed :: Monad m => Classed r m a -> r -> m a
runClassed = runReaderT

-- Classes
type Classes r = FreeT (Reader r) 
type IOClasses r = FreeT (Reader r) IOExcept

mapClasses :: Monad m => (forall a. m a -> n a) -> Classes r m b -> Classes r n b
mapClasses = hoistFreeT

withClasses :: Monad m => (r' -> r) -> Classes r m a -> Classes r' m a
withClasses = transFreeT . withReader

retractClasses :: Monad m => Classes r m a -> Classed r m a
retractClasses = retractT . transFree ftotm
  where
    ftotm :: Monad m => Classed Identity a -> Classed m a
    ftotm = mapClassed $ return . runIdentity 
    
runClasses :: Monad m => Classes r m a -> r -> m a
runClasses  = runClassed . retractClasses
    
zipClasses :: Monad m => Classes r m (a -> b) -> Classes r m a -> Classes r m b
FreeT mf `zipClasses` FreeT ma = FreeT $ zipF <$> mf <*> ma
  where
    zipF :: (Monad m, Applicative f) => FreeF f (a -> b) (FreeT f m (a -> b)) -> FreeF f a (FreeT f m a) -> FreeF f b (FreeT f m b) 
    Free fmf `zipF` Free fma = Free (zipClasses <$> fmf <*> fma)
    Free fmf `zipF` Pure a =  Free (fmap ($ a) <$> fmf)
    Pure f `zipF` Free fma = Free (fmap f <$> fma)
    Pure f `zipF` Pure a = Pure (f a)

liftClasses2 :: Monad m => (a -> b -> c) -> Classes r m a -> Classes r m b -> Classes r m c
liftClasses2 f ar br = (f <$> ar) `zipClasses` br

liftClassed :: Monad m => Classed r m a -> Classes r m a
liftClassed = FreeT . mapClassed Identity . fmap Pure
  where
    tmtofm :; Classed r m a -> Classed r Identity (m a)
    tmtofm = mapClassed Identity

askClasses :: Monad m => Classes r m r
askClasses = liftF ask

asksClasses :: Monad m => (r -> a) -> Classes r m a
asksClasses f = liftF (asks f)

lookupClassesWith :: k -> (r -> Vtable k r) -> IOClasses r Value
lookupClassesWith k f = asksClasses f >>= lookupVtable k

lookupClassesWithM :: k -> (r -> IOClasses r (Vtable k r)) -> IOClasses r Value
lookupClassesWithM k f = askClasses >>= f >>= lookupVtable k

-- Self
data Self = Self { unSelf :: ObjTable Self }

-- Scope
data Scope = Scope { penv :: RefTable Scope, cenv :: RefTable Scope, cobj :: ObjTable Scope, self :: ObjTable Scope }

lookupEnv :: T.Ident -> IOClasses Scope Value
lookupEnv k = lookupCenv `catchUnboundVar` (lookupCur `catchUnboundVar` lookupPenv)
  where
    lookupCenv = lookupClassesWith k cenv
    lookupCur = lookupClassesWith (T.Ref k) cobj
    lookupPenv = lookupClassesWith penv k

lookupSelf :: T.Name Value -> IOClasses Scope Value
lookupSelf k = lookupClassesWith k self
    
-- Eval
type Eval = State Integer

mapEval = mapState
runEval m = evalState m 0

-- Node
type NodeList r = ListT (IOClassed r)
type ScopeNodeList = NodeList Scope (RefTable Scope, ObjTable Scope)
type SelfNodeList = NodeList Self (ObjTable Self)
   
    
toNodeList :: Monoid a => IOClasses r a -> NodeList r a
toNodeList = iterTM (wrap . ftom) . hoistFreeT lift . fmap
  where
    ftom :: Monad m => Classed r Identity b -> Classed r m b
    ftom = mapClassed $ return . runIdentity
    
    wrap :: (Functor m, Monoid a) => m (ListT m a) -> ListT m a
    wrap = ListT . fmap (Cons mempty)
      

mergeNodeListWith :: (Maybe a -> Maybe b -> c) -> NodeList r a -> NodeList r b -> NodeList r c
mergeNodeListWith f = go
  where
    go xs ys = ListT $
      do{ sx <- next xs
        ; sy <- next ys
        ; return $ case (sx, sy) of
            (Cons x xs', Cons y ys') -> Cons (f (Just x) (Just y)) (go xs' ys')
            (_, Nil) -> map (flip f Nothing . Just) sx
            (Nil, _) -> map (f Nothing . Just) sy
            _ -> Nil
        }


newtype ConcatPair a b = CP (a, b)
instance (Monoid a, Monoid b) => Moniod (ConcatPair a b) where
  mempty = CP (mempty, mempty)
  CP (xa, xb) `mconcat` CP (ya, yb) = CP (xa `mconcat` ya, xb `mconcat` yb)

  
execScope :: NodeList Scope (RefTable Scope, ObjTable Scope) -> Scope -> NodeList Self (ObjTable Self)
execScope node (Scope penv _ _ self) = go node (Scope penv emptyVtable emptyVtable self)
  where
    go :: NodeList Scope (RefTable Scope, ObjTable Scope) -> Scope -> NodeList Self (ObjTable Self)
    go node (Scope penv cenv cobj self) = ListT . withClasses fixEnvs cenv $
      do{ step <- next node
        ; case step of
            Cons (cenv', cobj') xs' -> Cons self' xs''
              where
                xs'' = go xs' (fixEnv cenv cobj')
                self' = Self (fixEnvs cenv cobj')
            Nil -> Nil
        }
      where
        fixEnv :: RefTable Scope -> ObjTable Scope -> Scope
        fixEnv cenv cobj = Scope penv cenv cobj sub super
        
        fixEnvs :: RefTable Scope -> ObjTable Scope -> ObjTable Self
        fixEnvs cenv = go
          where
            go :: ObjTable Scope -> ObjTable Self
            go = withVtable f
            
            f :: Self -> Scope
            f (Self self) = fixEnv cenv (go self)
  
  
execNode :: NodeList Self (ObjTable Self) -> IOExcept Self
execNode node = go node (Self emptyVtable)
  where
    go :: NodeList Self (ObjTable Self) -> Self -> IOExcept Self
    go node self =
      do{ rest <- runClassed (next node) self
        ; case rest of
            Cons self' xs' -> go xs' self'
            Nil -> return self
        }
  
  
type Node = SelfNodeList
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

