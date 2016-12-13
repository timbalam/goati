{-# LANGUAGE Rank2Types #-}
module Eval
  ( evalRval
  , emptyNode
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
import Control.Monad.Trans.Class( lift )
import Data.IORef
  ( IORef
  , newIORef
  , readIORef
  , writeIORef
  )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval
  ( IOExcept
  , liftIO
  , Vtable
  , emptyVtable
  , concatVtable
  , lookupVtable
  , Vtables
  , inserts
  , concats
  , Env
  , Eval
  , Value(String, Number, Bool)
  , unNode
  , newNode
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
  
 
evalName :: T.Name T.Rval -> Env -> Eval (Vtable -> IOExcept (T.Name Value))
evalName (T.Key r) ie = evalRval r ie >>= \f -> fmap T.Key . f
evalName (T.Ref x) ie = return (\_ -> return $ T.Ref x)

evalRval :: T.Rval -> Env -> Eval (Vtable -> IOExcept Value)
evalRval (T.Number x) _ = return (\_ -> return $ Number x)
evalRval (T.String x) _ = return (\_ -> return $ String x)
evalRval (T.Rident x) ie = return (lookupIdent x ie)
  where
    lookupIdent :: T.Ident -> Env -> Vtable -> IOExcept Value
    lookupIdent x ie v =
      do{ f <- liftIO (readIORef ie)
        ; env <- f v
        ; x `lookupVtable` env
        }
evalRval (T.Rroute x) ie = evalRoute x ie
  where
    evalRoute :: T.Route T.Rval -> Env -> Eval (Vtable -> IOExcept Value)
    evalRoute (T.Route r key) ie =
      do{ vf <- evalRval r ie
        ; kf <- evalName key ie
        ; let lookupValue v =
            do{ k <- kf v
              ; val <- vf v
              ; v <- unNode val emptyVtable emptyVtable
              ; k `lookupVtable` v
              }
        ; return lookupValue
        }
    evalRoute (T.Atom key) ie =
      do{ kf <- evalName key ie
        ; let lookupValue v =
          do{ k <- kf v
            ; k `lookupVtable` v
            }
        ; return lookupValue
        }
evalRval (T.Rnode stmts) ie =
  do{ ie' <- return (newIORef return)
    ; (f, g) <- foldM (collectStmt ie') (emptyVtable, emptyVtable) stmts
  where
    collectStmt :: Env -> (Value -> Value, Value -> Value) -> T.Stmt -> Eval (Value -> Value, Value -> Value)
    collectStmt ie fg (T.Assign l r) = evalAssign l (evalRval r ie) ie fg
    collectStmt ie fg (T.Unpack r) =
      
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
    evalUnop :: T.Unop -> Value -> Eval Value
    evalUnop s (Number x) = primitiveNumberUnop s x
    evalUnop s (Bool x) = primitiveBoolUnop s x
    evalUnop s x = view (nodeLens . envLens (T.Key (unopSymbol s))) (return x) 
evalRval (T.Binop s x y) =
  do{ x' <- fixSelf (evalRval x)
    ; y' <- fixSelf (evalRval y)
    ; evalBinop s x' y'
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> Eval Value
    evalBinop s (Number x) (Number y) = primitiveNumberBinop s x y
    evalBinop s (Bool x) (Bool y) = primitiveBoolBinop s x y
    evalBinop s x y = view (nodeLens . envLens (T.Key resultSymbol)) (constructBinop s x y)
    
    constructBinop :: T.Binop -> Value -> Value -> Eval Value
    constructBinop s x y =
      fixSelf $ set
        (nodeLens . envLens (T.Key rhsSymbol))
        (return y) 
        (view (nodeLens . envLens (T.Key (binopSymbol s))) (return x))
      
evalAssign :: T.Lval -> Eval (Vtable -> IOExcept Value) -> Env -> (Value -> Value, Value -> Value) -> Eval (Value -> Value, Value -> Value)
evalAssign (T.Laddress x) mvf ie fg = evalAssignLaddress x mvf ie fg
  where
    evalAssignLaddress :: T.Laddress -> Eval (Value -> IOExcept Value) -> Env -> (Value -> Value, Value -> Value) -> Eval (Value -> Value, Value -> Value)
    evalAssignLaddress (T.Lident x) mvf ie (f, g) =
      do{ kf <- evalName x ie
        ; vf <- mvf
        ; let
            f' v v' = (++) <$> x v' <*> t v'
              where
                vt, x, vx, t :: Value -> IOExcept Vtable
                vt v' = (++) <$> unNode v v' <*> t v'
                x v' = do{ k <- kf (tmpNode vt); return [(k, vf v')] }
                vx v' = (++) <$> unNode v v' <*> x v'
                t v' = unNode (f (tmpNode vx)) v'
        ; return (f', g)
        }
    evalAssignLaddress (T.Lroute x) mvf ie fg = evalAssignRoute x mvf ie fg
    
    evalAssignIdent :: T.Ident -> (Value -> IOExcept) -> Env 
    evalAssignIdent x mvf ie 
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (Value -> IOExcept Value) -> Env -> (Value -> Value, Value -> Value) -> Eval (Value -> Value, Value -> Value)
    evalAssignRoute (T.Route l x) mvf ie fg =
      do{ kf <- evalName x ie
        ; vf <- mvf
        ; lvf <- lookupLaddress l ie
        ; let vf' v = 
        ; evalAssignLaddress l f ie fg
        }
    
    lookupLaddress :: T.Laddress -> Env -> Eval (Value -> IOExcept Value)
    lookupLaddress (T.Lident x) ie = liftIO (readIORef ie) >>= return . lookupIdent x
    lookupLaddress (T.Lroute r) ie = lookupRoute r ie
    
    lookupIdent :: T.Ident -> (Value -> IOExcept Vtable) -> Value -> IOExcept Value
    lookupIdent x f v =
      do{ env <- f v
        ; maybe 
            id
            (throwError $ E.UnboundVar "Unbound var" (show x))
            (env `lookup` (T.Ref x))
        }
        
    lookupRoute :: T.Route T.Laddress -> Env -> Eval (Value -> IOExcept Value)
    lookupRoute (T.Route l key) ie =
      do{ kf <- evalName key ie
        ; vf <- lookupLaddress l ie
        ; let lookupValue v =
            do{ k <- kf v
              ; f <- vf v
              ; xs <- unNode f f
              ; maybe
                  id
                  (throwError $ E.UnboundVar "Unbound var" (show k))
                  (xs `lookup` k)
              }
        ; return lookupValue
        }
    lookupRoute (T.Atom key) ie =
      do{ kf <- evalName key ie
        ; let lookupValue v =
            do{ k <- kf v
              ; xs <- unNode v v
              ; maybe
                  id
                  (throwError $ E.UnboundVar "Unbound var" (show k))
                  (xs `lookup` k)
              }
        ; return lookupValue
        }
      
    envLens :: T.Name T.Rval -> IORef Env -> IORef Value -> Lens' (Eval (IORef Env, IORef Value)) (Eval Value)
    envLens x ie is = lens (
    
    addressSetter :: T.Laddress -> IORef Env -> IORef Value -> Setter' (Eval (IORef Env, IORef Value)) (Eval Value)
    addressSetter (T.Lident x) ie is = fstLens . envLens (T.Ref x)
    addressSetter (T.Lroute x) = routeSetter x
    
    routeSetter :: T.Route T.Laddress -> Setter' (Eval Envs) (Eval Value)
    routeSetter (T.Route l key) = addressSetter l . setterLens key
    routeSetter (T.Atom  key) = selfSetter key
    
    selfSetter :: T.Name T.Rval -> Setter' (Eval Envs) (Eval Value)
    --selfSetter key = sets (\fmv -> over (fstLens . evalLens key) (\_ -> view (sndLens . evalLens key) getEnv) . over (sndLens . evalLens key) fmv)
    selfSetter key = sets (\fmv -> over (fstLens . evalLens key) fmv . over (sndLens . evalLens key) fmv)
    
    setterLens :: T.Name T.Rval -> Lens' (Eval Value) (Eval Value)
    setterLens key = lens (\mv -> view (nodeLens . evalLens key) mv `catchError` handleUnboundVar) (set (nodeLens . evalLens key))
    
    handleUnboundVar :: E.Error -> Eval r Value
    handleUnboundVar (E.UnboundVar _) = emptyNode
    handleUnboundVar err = throwError err
evalAssign (T.Lnode xs) mv es = 
  do{ (u, gs, es') <- foldM (\s x -> evalAssignStmt x mv s) (Nothing, [], es) xs
    ; maybe (return es') (\lhs -> guardedEvalAssign gs lhs mv es') u
    }
  where
    evalAssignStmt :: T.ReversibleStmt -> Eval Value -> (Maybe T.Lval, [T.PlainRoute], Envs) -> Eval (Maybe T.Lval, [T.PlainRoute], Envs)
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

    guardedEvalAssign :: [T.PlainRoute] -> T.Lval -> Eval Value -> Envs -> Eval Envs
    guardedEvalAssign gs lhs mv es =
      do{ let rem = foldl (\mv' keyroute -> unsetRoute keyroute mv') mv gs
        ; evalAssign lhs rem es
        }

    unsetRoute :: T.PlainRoute -> Eval Value -> Eval Value
    unsetRoute (T.PlainRoute (T.Atom key)) = over nodeLens (>>= evalDelete key)
    unsetRoute (T.PlainRoute (T.Route route key)) =
      over (foldPlainRoute (\l k -> l . evalLens k . nodeLens) nodeLens route) (>>= evalDelete key)
   
  
