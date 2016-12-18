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
  , lookupEnv
  , Vtables
  , emptyVtables
  , inserts
  , concats
  , unpacks
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
        ; lookupEnv (T.Ref x) f v
        }
evalRval (T.Rroute x) ie = evalRoute x ie
  where
    evalRoute :: T.Route T.Rval -> Env -> Eval (Vtable -> IOExcept Value)
    evalRoute (T.Route r x) ie =
      do{ vf <- evalRval r ie
        ; kf <- evalName x ie
        ; let lookupValue v =
            do{ k <- kf v
              ; val <- vf v
              ; v' <- unNode val emptyVtable emptyVtable
              ; k `lookupVtable` v'
              }
        ; return lookupValue
        }
    evalRoute (T.Atom x) ie =
      do{ kf <- evalName x ie
        ; let lookupValue v =
            do{ k <- kf v
              ; k `lookupVtable` v
              }
        ; return lookupValue
        }
evalRval (T.Rnode stmts) ie =
  do{ ie' <- return (newIORef return)
    ; (f, g) <- foldM (collectStmt ie') (emptyVtables, emptyVtables) stmts
    ; nn <- newNode
    ; let vf v =
            do{ pf <- liftIO (readIORef ie)
              ; penv <- pf v
              ; let f' v = concatVtable <$> f v <*> penv
              ; liftIO (writeIORef ie' f')
              ; return $ nn g
              }
    ; return vf
  where
    collectStmt :: Env -> (Vtable -> IOExcept Vtable, Vtables) -> T.Stmt -> Eval (Vtable -> IOExcept Vtable, Vtables)
    collectStmt ie fg (T.Assign l r) =
      do{ vf <- evalRval r ie
        ; evalAssign l vf ie fg
        }
    collectStmt ie (f, g) (T.Unpack r) =
      do{ vf <- evalRval r ie
        ; let vs l r = do{ val <- vf (l `concatVtable` r); unNode val emptyVtable emptyVtable }
        ; return (f, vs `concats` g)
        }
    collectStmt ie (f, g) (T.Eval r) =
      do[ vf <- evalRval r ie
        ; let vs l r = do{ _ <- vf (l `concatVtable` r); return emptyVtable }
        ; return (f, vs `concats` g)
        }
evalRval (T.App x y) ie =
  do{ xf <- evalRval x ie
    ; yf <- evalRval y ie
    , nn <- newNode
    ; let vf v =
            do{ x <- xf v
              ; y <- yf v
              ; return $ nn (unNode x `concats` unNode y)
              }
    ; return vf
    }
evalRval (T.Unop s x) ie =
  do{ xf <- evalRval x ie
    ; let vf v =
            do{ val <- xf v
              ; evalUnop s val
              }
    ; return vf
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop s (Number x) = primitiveNumberUnop s x
    evalUnop s (Bool x) = primitiveBoolUnop s x
    evalUnop s x =
      do{ v <- unNode x emptyVtable emptyVtable
        ; T.Key (unopSymbol s) `lookupVtable` v
        }
evalRval (T.Binop s x y) ie =
  do{ xf <- evalRval x ie
    ; yf <- evalRval y ie
    ; let vf v =
            do{ xval <- xf v
              ; yval <- yf v
              ; evalBinop s xval yval
              }
    ; return vf
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop s (Number x) (Number y) = primitiveNumberBinop s x y
    evalBinop s (Bool x) (Bool y) = primitiveBoolBinop s x y
    evalBinop s x y = 
      do{ xv <- unNode x emptyVtable emptyVtable
        ; xop <- T.Key (binopSymbol s) `lookupVtable` xv
        ; let vs = inserts (\_ -> return $ T.Key rhsSymbol) (\_ -> return $ y) `concats` unNode xop
        ; v <- vs emptyVtable emptyVtable
        ; T.Key resultSymbol `lookupVtable` v
        }
        
        
evalAssign :: T.Lval -> (Vtable -> IOExcept Value) -> Env -> (Vtable -> IOExcept Vtable, Vtables) -> Eval (Vtable -> IOExcept Vtable, Vtables)
evalAssign (T.Laddress x) vf ie fg = evalAssignLaddress x mvf ie fg
  where
    evalAssignLaddress :: T.Laddress -> (Vtable -> IOExcept Value) -> Env -> (Vtable -> IOExcept Vtable, Vtables) -> Eval (Vtable -> IOExcept Vtable, Vtables)
    evalAssignLaddress (T.Lident x) vf ie (f, g) =
      do{ let f' v = f v >>= insertVtable (T.Ref x) vf
        ; return (f', g)
        }
    evalAssignLaddress (T.Lroute x) vf ie fg = evalAssignRoute x vf ie fg
    
    
    evalAssignRoute :: T.Route T.Laddress -> (Vtable -> IOExcept Value) -> Env -> (Vtable -> IOExcept Vtable, Vtables) -> Eval (Vtable -> IOExcept Vtable, Vtables)
    evalAssignRoute (T.Route l x) vf ie fg =
      do{ kf <- evalName x ie
        ; nn <- newNode
        ; let lvf = lookupLaddress l ie
              vf' v =
                do{ ws <- catchError (unNode <$> lvf v) handleUnboundVar
                  ; let kf' _ = kf v
                  ; nn $ inserts kf' vf `concats` ws
                  }
        ; evalAssignLaddress l vf' ie fg
        }
    evalAssignRoute (T.Atom x) vf ie fg =
      do{ kf <- evalName x ie
        ; let g' = inserts kf vf `concats` g
              f' v =
                do{ env <- f v
                  ; k <- kf v
                  ; let vf' _ = k `lookupVtable` v
                  ; insertVtable k vf' env
                  }
        ; return (f', g')
        }
        
        
    lookupLaddress :: T.Laddress -> Env -> Vtable -> IOExcept Value
    lookupLaddress (T.Lident x) ie v =
      do{ f <- liftIO (readIORef ie)
        ; lookupEnv (T.Ref x) f v
        }
    lookupLaddress (T.Lroute r) ie vs = lookupRoute r ie
       
       
    lookupRoute :: T.Route T.Laddress -> Env -> Vtable -> IOExcept Value
    lookupRoute (T.Route l key) ie v =
      do{ kf <- evalName key ie
        ; vf <- lookupLaddress l ie
        ; let lookupValue v =
                do{ k <- kf v
                  ; val <- vf v
                  ; v' <- unNode val emptyVtable emptyVtable
                  ; k `lookupVtable` v'
                  }
        ; return lookupValue
        }
    lookupRoute (T.Atom key) ie =
      do{ kf <- evalName key ie
        ; let lookupValue v =
                do{ k <- kf v
                  ; k `lookupVtable` v
                  }
        ; return lookupValue
        }
      
      
    handleUnboundVar :: E.Error -> IOExcept Vtables
    handleUnboundVar (E.UnboundVar _ _) = return emptyVtables
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
   
  
