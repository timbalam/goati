module Eval
  ( eval
  )
where
import qualified Types.Syntax as T
import qualified Error as E
import Control.Monad.Except
 ( ExceptT
 )
import Control.Monad.Trans.State
 ( StateT
 )

 --
type Assoc a = [(T.Name Value, a)]
 
assocLookup :: MonadError E.Error m => T.Name Value -> Assoc a -> m a
assocLookup key =  maybe (throwError E.UnboundVar) return . lookup key

assocInsert :: MonadError E.Error m => T.Name Value -> a -> Assoc a -> m (Assoc a)
assocInsert key value e = return ((key, value):e)

assocLens :: MonadError E.Error m => T.Name Value -> Lens' (m (Assoc a)) (m a)
assocLens key = lens (>>= assocLookup key) (\mxs ma -> do{ xs <- mxs; a <- ma; assocInsert key a xs})

assocDelete :: MonadError E.Error m => T.Name Value -> Assoc a -> m (Assoc a)
assocDelete key = return . filter ((key ==) . fst)

assocConcat :: MonadError E.Error m => Assoc a -> Assoc a -> m (Assoc a)
assocConcat = liftM2 (++)

--
type Except = Either E.Error
type IOExcept = ExceptT E.Error IO
type Env = Assoc Value
type Eval = StateT Integer (ReaderT Env IOExcept)
data Value = String String | Number Double | Node Integer (Eval Env)

instance Eq Value where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Node x _ _ == Node x' _ _ = x == x'
  _ == _ = False
  
newNode :: Eval Env -> Eval Value
newNode f =
  do{ i <- get
    ; modify (+1)
    ; return (Node i f)
    }
 
unNode :: Value -> Eval Env
unNode (String x) = return (StringEnv x)
unNode (Number x) = return (NumberEnv x)
unNode (Node _ m) = m 
    
-- My mini lens library
type Lens' s a = Functor f => (a -> f a) -> s -> f s
type Setter' s a = (a -> Identity a) -> s -> Identity s 

lens :: (s -> a) -> (s -> a -> s) -> Lens' s a
lens get set f s = set s `fmap` f (get s)

sets :: ((a -> a) -> s -> s) -> Setter' s a 
sets f g = Identity . f (runIdentity . g)

view :: Lens' s a -> s -> a
view lens = getConst . lens Const

over :: Setter' s a -> (a -> a) -> s -> s
over lens f = runIdentity . l (Identity . f)

set :: Setter' s a -> a -> s -> s
set lens b = runIdentity . l (\_ -> Identity b)
  
-- 
emptyNode :: Eval Value
emptyNode = newNode $ return []
         
nodeApply :: Value -> Value -> Eval Value
nodeApply f g =
  newNode $
    do{ x <- unNode f >>= getSelf >>= unNode
      ; y <- unNode g >>= getSelf >>= unNode
      ; set (nodeLens . lenSelf) (x `assocConcat` y) getEnv
      } 
      
nodeLens :: Lens' (Eval Value) (Eval Env)
nodeLens = lens (>>= unNode) (\_ -> newNode)
 
getEnv :: Eval Env
getEnv = lift . ask

fixEnv ::
  Eval Env     -- Compute the enviroment 
  -> Eval Env  -- Make the environment available to itself during computation
fixEnv m = mfix bindEnv
  where
    bindEnv :: Env -> Eval Env
    bindEnv e = mapStateT (withReaderT (setSelf e . getSelf)) m

lensSelf :: Lens' (Eval Env) (Eval Value)
lensSelf = evalLens (T.Name SelfSymbol)

getSelf :: Env -> Eval Value
getSelf e = view lensSelf (return e)

setSelf :: Env -> Value -> Eval Env
setSelf e s = set lensSelf (return e) (return s)

fixSelf :: Eval Env -> Eval Env
fixSelf m = mfix bindSelf
  where
    bindSelf :: Env -> Eval Env
    bindSelf e =
        mapStateT (withReaderT (\e' -> setSelf e' (getSelf e))) m
     
toEnv :: Value -> Eval Env
toEnv = fixSelf . unNode
    
evalName :: T.Name T.Rval -> Eval (T.Name Value)
evalName = mapMName evalRval
  where
    mapMName :: Monad m => (a -> m b) -> T.Name a -> m (T.Name b)
    mapMName f (T.Key r)   = f r >>= return . T.Key
    mapMName _ k@(T.Ref _) = return k     

evalLens :: T.Name T.Rval -> Lens' (Eval (Assoc a)) (Eval a)
evalLens key =
  lens
    (\mxs -> do{ key' <- evalName key; view (assocLens key') mxs })
    (\mxs ma -> do{ key' <- evalName key; set (assocLens key') mxs ma })

evalDelete :: T.Name T.Rval -> Assoc a -> Eval (Assoc a)
evalDelete key e = 
  do{ key' <- evalName key
    ; assocDelete key' e
    }
  
evalRval :: T.Rval -> Eval Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = view (evalLens (T.Ref x)) getEnv
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval Value
    evalRoute (T.Route r key) =view (evalLens key) (evalRval r >>= toEnv)
    evalRoute (T.Atom key) = view (evalLens key) (view lensSelf getEnv >>= toEnv)
evalRval (T.Rnode stmts) =
  do{ p <- set lensSelf emptyNode getEnv
    ; return . newNode . fixEnv $ foldM collectStmt p stmts
    }
  where
    collectStmt :: Env -> T.Stmt -> Eval Env
    collectStmt e (T.Assign l r) = do{ x <- evalRval r; evalAssign l x e }
    collectStmt e (T.Unpack r) = 
      over (nodeLens . lensSelf) (\mse -> do{ x <- evalRval r >>= toEnv; se <- mse; x `assocConcat` se }) (return e)
    collectStmt e (T.Eval r) = evalRval r >>= toEnv >> return e
evalRval (T.App x y) =
  do{ x' <- evalRval x
    ; y' <- evalRval y
    ; x' `nodeApply` y'
    }
evalRval (T.Unop s x) = evalRval x >>= evalUnop s
  where
    evalUnop :: T.Unop -> Value -> Eval Value
    evalUnop s (T.Number x) = primitiveNumberUnop s x
    evalUnop s x = view (evalLens . T.Key $ unopSymbol s) (toEnv x) 
evalRval (T.Binop s x y) =
  do{ x' <- evalRval x
    ; y' <- evalRval y
    ; evalBinop s x' y'
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> Eval Value
    evalBinop s (T.Number x) (T.Number y) = primitiveNumberBinop s x y
    evalBinop s x y = view evalLens (T.Key resultSymbol) (constructBinop s x y)
    
    constructBinop :: T.Binop -> Value -> Value -> Eval Value
    constructBinop s x y =
      set
        (assocLens (T.Key rhsSymbol) . nodeLens . lensSelf)
        (return y) 
        (view (evalLens (T.Key (binopSymbol s))) (return x) >>= unNode >>= getSelf >>= unNode)
      
evalAssign :: T.Lval -> Value -> Env -> Eval Env
evalAssign (T.Laddress x) value e = set (addressSetter x) (return value) (return e)
  where
    addressSetter :: T.Laddress -> Setter' (Eval Env) (Eval Value)
    addressSetter (T.Lident x) = assocLens (T.Ref x)
    addressSetter (T.Lroute x) = routeSetter x
    
    routeSetter :: T.Route T.Laddress -> Setter' (Eval Env) (Eval Value)
    routeSetter (T.Route l key) = creatorLens key . addressSetter l
    routeSetter (T.Atom  key) = selfSetter key
    
    selfSetter :: T.Name Value -> Setter' (Eval Env) (Eval Env)
    selfSetter key = sets (\fme -> set (evalLens key) fme . set (evalLens key . nodeLens . lensSelf) fme )
    
    setterLens :: T.Name T.Rval -> Lens' (Eval Value) (Eval Value)
    setterLens key = lens (\mv -> view (evalLens key . nodeLens) mv `catchError` handleUnboundVar) (set (evalLens key))
    
    handleUnboundVar :: E.Error -> Eval Value
    handleUnboundVar E.UnboundVar = emptyNode
    handleUnboundVar err = throwError err
evalAssign (T.Lnode xs) value e = 
  do{ (u, gs, e') <- foldM (\s x -> evalAssignStmt x value s) (Nothing, [], e) xs
    ; maybe (return e') (\lhs -> guardedEvalAssign gs lhs value e') u
    }
  where
    evalAssignStmt :: T.ReversibleStmt -> T.Value -> (Maybe T.Lval, [T.PlainRoute], Env) -> Eval (Maybe T.Lval, [T.PlainRoute], Env)
    evalAssignStmt (T.ReversibleAssign keyroute lhs) value (u, gs, e) =
      do{ value' <- get (foldPlainRoute (\l k -> evalLens k . l) . nodeLens) value
        ; e' <- evalAssign lhs value' e
        ; return (u, keyroute:gs, e')
        }
    evalAssignStmt (T.ReversibleUnpack lhs) _ (Nothing, gs, e) = (Just lhs, gs, e)
    evalAssignStmt (T.ReversibleUnpack _) _ (Just _, _, _) = error "Multiple unpack stmts"
    
    foldPlainRoute :: (a -> T.Name T.Rval -> a) -> a -> T.PlainRoute -> a
    foldPlainRoute f a (T.PlainRoute key@(T.Atom _)) = f a key
    foldPlainRoute f a (T.PlainRoute (T.Route l key)) = f (foldPlainRoute f a l) key

    guardedEvalAssign :: [T.PlainRoute] -> T.Lval -> T.Rval -> Env -> Eval Env
    guardedEvalAssign gs (T.Laddress x) value e =
      do{ value' <- evalRval value
        ; rem <- foldM (\e keyroute -> unsetRoute keyroute e) value' gs
        ; evalAssign x rem e
        }

    unsetRoute :: T.PlainRoute -> Env -> Eval Env
    unsetRoute (T.PlainRoute key@(T.Atom _)) = evalDelete (T.Ref x)
    unsetRoute (T.PlainRoute (T.Route route key)) =
      set (nodeLens . foldPlainRoute (\l k -> evalLens k . l)) (>>= evalDelete key)
   
  
