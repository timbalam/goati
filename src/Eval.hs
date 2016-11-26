{-# LANGUAGE Rank2Types #-}
module Eval
  ( evalRval
  , emptyNode
  , lensSelf
  , envLens
  )
where
import Control.Monad.Except
  ( throwError
  , catchError
  )
import Control.Monad
  ( liftM2
  , foldM
  )
import Control.Monad.Trans.Class
  ( lift
  )
import Control.Monad.State
  ( mapStateT
  )
import Control.Monad.Reader
  ( withReaderT
  , ask
  )
import Control.Monad.Fix
  ( mfix
  )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval
  ( Env
  , CalcValue(..)
  , Value(..)
  , unNode
  , newNode
  , Eval
  , getEnv
  , withEnv
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
  )
import Utils.Lens
  ( Lens'
  , Setter'
  , lens
  , sets
  , view
  , over
  , set
  )
import Utils.Assoc
  ( assocLookup
  , assocInsert
  , assocDelete
  , assocConcat
  , assocLens
  , showAssoc
  )
 
calcValueLens :: Lens' (Eval CalcValue) (Eval Value)
calcValueLens = lens (>>= runCalcValue) (\_ -> return . CalcValue)

envLens :: (T.Name Value) -> Lens' (Eval Env) (Eval Value)
envLens key = assocLens key . calcValueLens

nodeLens :: Lens' (Eval Value) (Eval Env)
nodeLens = lens (>>= return . unNode) (\_ -> (>>= newNode))

emptyNode :: Eval Value
emptyNode = newNode []
         
nodeApply :: Value -> Value -> Eval Value
nodeApply f g =
  do{ xs <- (unNode f) `assocConcat` (unNode g)
    ; newNode xs
    }
      
fixEnv ::
  Eval Env     -- Compute the enviroment 
  -> Eval Env  -- Make the environment available to itself during computation
fixEnv m = mfix bindEnv
  where
    bindEnv :: Env -> Eval Env
    bindEnv e = set lensSelf (view lensSelf getEnv) (return e) >>= \e' -> withEnv (const e') m

lensSelf :: Lens' (Eval Env) (Eval Value)
lensSelf = envLens (T.Key selfSymbol)

fixSelf :: Eval Value -> Eval Value
fixSelf m = mfix bindSelf
  where
    bindSelf :: Value -> Eval Value
    bindSelf s = set lensSelf (return s) getEnv >>= \e' -> withEnv (const e') m
     
extractSelf :: Eval Value -> Eval Value
extractSelf mv =
  do{ e <- set lensSelf emptyNode getEnv
    ; withEnv (const e) (fixSelf mv)
    }
-- extractSelf = view (lensSelf . nodeLens) . fixSelf
    
evalName :: T.Name T.Rval -> Eval (T.Name Value)
evalName = mapMName evalRval
  where
    mapMName :: Monad m => (a -> m b) -> T.Name a -> m (T.Name b)
    mapMName f (T.Key r) = f r >>= return . T.Key
    mapMName _ (T.Ref x) = return (T.Ref x)   

evalLens :: T.Name T.Rval -> Lens' (Eval Env) (Eval Value)
evalLens key =
  lens
    (\mxs -> do{ key' <- evalName key; view (envLens key') mxs })
    (\mxs ma -> do{ key' <- evalName key; set (envLens key') ma mxs })

evalDelete :: T.Name T.Rval -> Env -> Eval Env
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
    evalRoute (T.Route r key) = view (nodeLens . evalLens key) (extractSelf (evalRval r))
    evalRoute (T.Atom key) = view (nodeLens . evalLens key) (extractSelf (view lensSelf getEnv))
evalRval (T.Rnode stmts) =
  do{ e <- getEnv
    ; view lensSelf (fixEnv (foldM collectStmt e stmts))
    }
  where
    collectStmt :: Env -> T.Stmt -> Eval Env
    collectStmt e (T.Assign l r) = evalAssign l (evalRval r) e
    collectStmt e (T.Unpack r) = 
      over
        lensSelf
        (\ms -> do{ x <- extractSelf (evalRval r); s <- ms; x `nodeApply` s })
        (return e)
    collectStmt e (T.Eval r) = evalRval r >> return e
evalRval (T.App x y) =
  do{ x' <- evalRval x
    ; y' <- evalRval y
    ; x' `nodeApply` y'
    }
evalRval (T.Unop s x) = extractSelf (evalRval x) >>= evalUnop s
  where
    evalUnop :: T.Unop -> Value -> Eval Value
    evalUnop s (Number x) = primitiveNumberUnop s x
    evalUnop s (Bool x) = primitiveBoolUnop s x
    evalUnop s x = view (nodeLens . envLens (T.Key (unopSymbol s))) (return x) 
evalRval (T.Binop s x y) =
  do{ x' <- extractSelf (evalRval x)
    ; y' <- extractSelf (evalRval y)
    ; evalBinop s x' y'
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> Eval Value
    evalBinop s (Number x) (Number y) = primitiveNumberBinop s x y
    evalBinop s (Bool x) (Bool y) = primitiveBoolBinop s x y
    evalBinop s x y = view (nodeLens . envLens (T.Key resultSymbol)) (constructBinop s x y)
    
    constructBinop :: T.Binop -> Value -> Value -> Eval Value
    constructBinop s x y =
      extractSelf $ set
        (nodeLens . envLens (T.Key rhsSymbol))
        (return y) 
        (view (nodeLens . envLens (T.Key (binopSymbol s))) (return x))
      
evalAssign :: T.Lval -> Eval Value -> Env -> Eval Env
evalAssign (T.Laddress x) mv e = set (addressSetter x) mv (return e)
  where
    addressSetter :: T.Laddress -> Setter' (Eval Env) (Eval Value)
    addressSetter (T.Lident x) = envLens (T.Ref x)
    addressSetter (T.Lroute x) = routeSetter x
    
    routeSetter :: T.Route T.Laddress -> Setter' (Eval Env) (Eval Value)
    routeSetter (T.Route l key) = addressSetter l . setterLens key
    routeSetter (T.Atom  key) = selfSetter key
    
    selfSetter :: T.Name T.Rval -> Setter' (Eval Env) (Eval Value)
    selfSetter key = sets (\fmv -> over (evalLens key) fmv . over (lensSelf . nodeLens . evalLens key) fmv)
    
    setterLens :: T.Name T.Rval -> Lens' (Eval Value) (Eval Value)
    setterLens key = lens (\mv -> view (nodeLens . evalLens key) mv `catchError` handleUnboundVar) (set (nodeLens . evalLens key))
    
    handleUnboundVar :: E.Error -> Eval Value
    handleUnboundVar (E.UnboundVar _) = emptyNode
    handleUnboundVar err = throwError err
evalAssign (T.Lnode xs) mv e = 
  do{ (u, gs, e') <- foldM (\s x -> evalAssignStmt x mv s) (Nothing, [], e) xs
    ; maybe (return e') (\lhs -> guardedEvalAssign gs lhs mv e') u
    }
  where
    evalAssignStmt :: T.ReversibleStmt -> Eval Value -> (Maybe T.Lval, [T.PlainRoute], Env) -> Eval (Maybe T.Lval, [T.PlainRoute], Env)
    evalAssignStmt (T.ReversibleAssign keyroute lhs) mv (u, gs, e) =
      do{ let value' = view (foldPlainRoute (\l k -> l . nodeLens . evalLens k) id keyroute) mv
        ; e' <- evalAssign lhs value' e
        ; return (u, keyroute:gs, e')
        }
    evalAssignStmt (T.ReversibleUnpack lhs) _ (Nothing, gs, e) = return (Just lhs, gs, e)
    evalAssignStmt (T.ReversibleUnpack _) _ (Just _, _, _) = error "Multiple unpack stmts"
    
    foldPlainRoute :: (a -> T.Name T.Rval -> a) -> a -> T.PlainRoute -> a
    foldPlainRoute f a (T.PlainRoute (T.Atom key)) = f a key
    foldPlainRoute f a (T.PlainRoute (T.Route l key)) = f (foldPlainRoute f a l) key

    guardedEvalAssign :: [T.PlainRoute] -> T.Lval -> Eval Value -> Env -> Eval Env
    guardedEvalAssign gs lhs mv e =
      do{ let rem = foldl (\e keyroute -> unsetRoute keyroute e) mv gs
        ; evalAssign lhs rem e
        }

    unsetRoute :: T.PlainRoute -> Eval Value -> Eval Value
    unsetRoute (T.PlainRoute (T.Atom key)) = over nodeLens (>>= evalDelete key)
    unsetRoute (T.PlainRoute (T.Route route key)) =
      over (foldPlainRoute (\l k -> l . evalLens k . nodeLens) nodeLens route) (>>= evalDelete key)
   
  
