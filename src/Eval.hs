{-# LANGUAGE Rank2Types #-}
module Eval
  ( evalRval
  , emptyNode
  , fstLens
  , sndLens
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
  , Envs
  , CalcValue(..)
  , Value(..)
  , unNode
  , newNode
  , Eval
  , Eval'
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
 
calcValueLens :: Lens' (Eval' CalcValue) (Eval' Value)
calcValueLens = lens (>>= runCalcValue) (\_ -> return . CalcValue)

envLens :: (T.Name Value) -> Lens' (Eval' Env) (Eval' Value)
envLens key = assocLens key . calcValueLens

nodeLens :: Lens' (Eval r Value) (Eval r Env)
nodeLens = lens (>>= return . unNode) (\_ -> (>>= newNode))

emptyNode :: Eval r Value
emptyNode = newNode []

nodeApply :: Value -> Value -> Eval r Value
nodeApply f g =
  do{ xs <- (unNode f) `assocConcat` (unNode g)
    ; newNode xs
    }

fstLens :: Lens' (Eval r Envs) (Eval r Env)
fstLens = lens (>>= return . fst) (\mes me -> fmap (,) me <*> fmap snd mes)

sndLens :: Lens' (Eval r Envs) (Eval r Env)
sndLens = lens (>>= return . snd) (\mes ms -> fmap (,) (fmap fst mes) <*> ms)
      
fixEnv ::
  Eval' Envs     -- Compute the enviroment 
  -> Eval' Envs  -- Make the environment available to itself during computation
fixEnv = mfix . bindEnv

bindEnv :: Eval' a -> Envs -> Eval' a
bindEnv m (e, _) = getEnv >>= \(_, s) -> withEnv (const (e, s)) m

fixSelf :: Eval' Value -> Eval' Value
fixSelf = mfix . bindSelf

bindSelf :: Eval' a -> Value -> Eval' a
bindSelf m s = getEnv >>= \(e, _) -> withEnv (const (e, unNode s)) m
    
evalName :: T.Name T.Rval -> Eval' (T.Name Value)
evalName = mapMName evalRval
  where
    mapMName :: Monad m => (a -> m b) -> T.Name a -> m (T.Name b)
    mapMName f (T.Key r) = f r >>= return . T.Key
    mapMName _ (T.Ref x) = return (T.Ref x)   

evalLens :: T.Name T.Rval -> Lens' (Eval' Env) (Eval' Value)
evalLens key =
  lens
    (\mxs -> do{ key' <- evalName key; view (envLens key') mxs })
    (\mxs ma -> do{ key' <- evalName key; set (envLens key') ma mxs })

evalDelete :: T.Name T.Rval -> Env -> Eval' Env
evalDelete key e = 
  do{ key' <- evalName key
    ; assocDelete key' e
    }
  
evalRval :: T.Rval -> Eval' Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = view (fstLens . evalLens (T.Ref x)) getEnv
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval' Value
    evalRoute (T.Route r key) = view (nodeLens . evalLens key) (fixSelf (evalRval r))
    evalRoute (T.Atom key) = view (sndLens . evalLens key) getEnv
evalRval (T.Rnode stmts) =
  do{ (e, _) <- getEnv
    ; s' <- view sndLens $ fixEnv (foldM collectStmt (e, []) stmts)
    ; newNode s'
    }
  where
    collectStmt :: Envs -> T.Stmt -> Eval' Envs
    collectStmt es (T.Assign l r) =
      do{ es' <- getEnv;  evalAssign l (withEnv (const es') (evalRval r)) es }
    collectStmt es (T.Unpack r) = 
      over
        sndLens
        (\ms -> do{ x <- fixSelf (evalRval r); s <- ms; unNode x `assocConcat` s })
        (return es)
    collectStmt es (T.Eval r) = evalRval r >> return es
evalRval (T.App x y) =
  do{ x' <- evalRval x
    ; y' <- evalRval y
    ; y' `nodeApply` x'
    }
evalRval (T.Unop s x) = fixSelf (evalRval x) >>= evalUnop s
  where
    evalUnop :: T.Unop -> Value -> Eval' Value
    evalUnop s (Number x) = primitiveNumberUnop s x
    evalUnop s (Bool x) = primitiveBoolUnop s x
    evalUnop s x = view (nodeLens . envLens (T.Key (unopSymbol s))) (return x) 
evalRval (T.Binop s x y) =
  do{ x' <- fixSelf (evalRval x)
    ; y' <- fixSelf (evalRval y)
    ; evalBinop s x' y'
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> Eval' Value
    evalBinop s (Number x) (Number y) = primitiveNumberBinop s x y
    evalBinop s (Bool x) (Bool y) = primitiveBoolBinop s x y
    evalBinop s x y = view (nodeLens . envLens (T.Key resultSymbol)) (constructBinop s x y)
    
    constructBinop :: T.Binop -> Value -> Value -> Eval' Value
    constructBinop s x y =
      fixSelf $ set
        (nodeLens . envLens (T.Key rhsSymbol))
        (return y) 
        (view (nodeLens . envLens (T.Key (binopSymbol s))) (return x))
      
evalAssign :: T.Lval -> Eval' Value -> Envs -> Eval' Envs
evalAssign (T.Laddress x) mv es = set (addressSetter x) mv (return es)
  where
    addressSetter :: T.Laddress -> Setter' (Eval' Envs) (Eval' Value)
    addressSetter (T.Lident x) = fstLens . envLens (T.Ref x)
    addressSetter (T.Lroute x) = routeSetter x
    
    routeSetter :: T.Route T.Laddress -> Setter' (Eval' Envs) (Eval' Value)
    routeSetter (T.Route l key) = addressSetter l . setterLens key
    routeSetter (T.Atom  key) = selfSetter key
    
    selfSetter :: T.Name T.Rval -> Setter' (Eval' Envs) (Eval' Value)
    --selfSetter key = sets (\fmv -> over (fstLens . evalLens key) (\_ -> view (sndLens . evalLens key) getEnv) . over (sndLens . evalLens key) fmv)
    selfSetter key = sets (\fmv -> over (fstLens . evalLens key) fmv . over (sndLens . evalLens key) fmv)
    
    setterLens :: T.Name T.Rval -> Lens' (Eval' Value) (Eval' Value)
    setterLens key = lens (\mv -> view (nodeLens . evalLens key) mv `catchError` handleUnboundVar) (set (nodeLens . evalLens key))
    
    handleUnboundVar :: E.Error -> Eval r Value
    handleUnboundVar (E.UnboundVar _) = emptyNode
    handleUnboundVar err = throwError err
evalAssign (T.Lnode xs) mv es = 
  do{ (u, gs, es') <- foldM (\s x -> evalAssignStmt x mv s) (Nothing, [], es) xs
    ; maybe (return es') (\lhs -> guardedEvalAssign gs lhs mv es') u
    }
  where
    evalAssignStmt :: T.ReversibleStmt -> Eval' Value -> (Maybe T.Lval, [T.PlainRoute], Envs) -> Eval' (Maybe T.Lval, [T.PlainRoute], Envs)
    evalAssignStmt (T.ReversibleAssign keyroute lhs) mv (u, gs, es) =
      do{ let value' = view (foldPlainRoute (\l k -> l . nodeLens . evalLens k) id keyroute) mv
        ; es' <- evalAssign lhs value' es
        ; return (u, keyroute:gs, es')
        }
    evalAssignStmt (T.ReversibleUnpack lhs) _ (Nothing, gs, es) = return (Just lhs, gs, es)
    evalAssignStmt (T.ReversibleUnpack _) _ (Just _, _, _) = error "Multiple unpack stmts"
    
    foldPlainRoute :: (a -> T.Name T.Rval -> a) -> a -> T.PlainRoute -> a
    foldPlainRoute f a (T.PlainRoute (T.Atom key)) = f a key
    foldPlainRoute f a (T.PlainRoute (T.Route l key)) = f (foldPlainRoute f a l) key

    guardedEvalAssign :: [T.PlainRoute] -> T.Lval -> Eval' Value -> Envs -> Eval' Envs
    guardedEvalAssign gs lhs mv es =
      do{ let rem = foldl (\mv' keyroute -> unsetRoute keyroute mv') mv gs
        ; evalAssign lhs rem es
        }

    unsetRoute :: T.PlainRoute -> Eval' Value -> Eval' Value
    unsetRoute (T.PlainRoute (T.Atom key)) = over nodeLens (>>= evalDelete key)
    unsetRoute (T.PlainRoute (T.Route route key)) =
      over (foldPlainRoute (\l k -> l . evalLens k . nodeLens) nodeLens route) (>>= evalDelete key)
   
  
