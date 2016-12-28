module Eval
  ( evalRval
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

type Gets' s a = s -> a
type Sets' s a = (a -> a) -> s -> s
newtype NEnv = NEnv { getNEnv :: IOF Vtable }
newtype NVtables = NVtables { getNVtables :: Vtables }
type StateF = ObjF (State (NEnv, NVtables))
newtype Rem = Rem { getRem :: IOF Value }
type StateUF = ObjF (StateT Rem StateF)
  
  
viewValueF :: IOF (T.Name Value) -> Gets' (IOF Value) (IOF Value)
viewValueF kf vf =
  do{ env <- ask
    ; lift $ lookupValueR (runReaderT kf env) (runReaderT vf env)
    }


overValueF :: IOF (T.Name Value) -> Eval (Sets' (IOF Value) (IOF Value))
overValueF kf =
  do{ nn <- newNode
    ; let over f vf =
            do{ k <- kf
              ; val <- f (viewValueF kf vf)
              ; vs <- unNode <$> vf
              ; return $ nn (inserts (return k) (return val) vs)
              }
    ; return over
    }


viewSelfF :: IOF (T.Name Value) -> IOF Value
viewSelfF kf = kf >>= lift . lookupR

 
evalName :: T.Name T.Rval -> Eval (IOF (T.Name Value))
evalName (T.Key r) = (T.Key <$>) <$> evalRval r
evalName (T.Ref x) = return . return $ T.Ref x


evalRval :: T.Rval -> Eval (IOF Value)
evalRval (T.Number x) = return . return $ Number x
evalRval (T.String x) = return . return $ String x
evalRval (T.Rident x) = return (lookupF (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (IOF Value)
    evalRoute (T.Route r x) = viewValueF <$> evalName x <*> evalRval r
    evalRoute (T.Atom x) = viewSelfF <$> evalName x
evalRval (T.Rnode stmts) =
  do{ b <- foldr (>>) (return ()) <$> sequence (collectStmt `map` stmts)
    ; nn <- newNode
    ; return $
        do{ env <- ask
          ; (self, super) <- lift ask
          ; p <- lift env
          ; let (f, vs) = execValueB (runObjR b f' (self super)) (return p, emptyVtables)
                f' = CEnv (getSelf self `concatVtable` f)
          ; return $ nn vs
          }
    }
  where
    collectStmt :: T.Stmt -> Eval (ObjR ValueB ())
    collectStmt (T.Assign l r) = evalAssign l <*> evalRval r
    collectStmt (T.Unpack r) = mapObjR unpack <$> evalRval r
      where
        unpack :: IOExcept Value -> ValueB ()
        unpack mv =
          do{ (f, vs) <- get
            ; put (f, unpacks mv vs)
            }
    collectStmt (T.Eval r) = mapObjR . const (return ()) <$> evalRval r
evalRval (T.App x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; nn <- newNode
    ; return $ 
        do{ v <- vf
          ; w <- wf
          ; return $ nn (unNode w `concats` unNode v)
          }
    }
evalRval (T.Unop sym x) =
  do{ vf <- evalRval x
    ; return $
        do{ v <- vf
          ; lift $ evalUnop sym v
          }
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupVtables` unNode x
evalRval (T.Binop sym x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; return $
        do{ v <- vf
          ; w <- wf
          ; lift $ evalBinop sym v w
          }
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xop <- T.Key (binopSymbol sym) `lookupVtables` unNode x
        ; let vs = inserts (return $ T.Key rhsSymbol) (return y) (unNode xop)
        ; T.Key resultSymbol `lookupVtables` vs
        }
        
        
evalAssign :: T.Lval -> Eval (IOF Value -> StateF ())
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (IOF Value -> StateF ())
    evalAssignLaddress (T.Lident x) =
      return $ \ vf ->
        do{ let k = T.Ref x
          ; env <- ask
          ; (NEnv f, NVtables vs) <- liftObjF get
          ; let f' = insertVtable k (runReaderT vf env) <$> f
          ; liftObjF $ put (NEnv f', NVtables vs)
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (IOF Value -> StateF ())
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; b <- lookupLaddress l
        ; assignLhs <- evalAssignLaddress l
        ; kf <- evalName x
        ; return $ \wf ->
            do{ mv <- b
              ; mvf <- mapObjF return $
                  do{ k <- kf
                    ; w <- wf
                    ; vs <- catchUnboundVar (unNode <$> mv) (return emptyVtables)
                    ; return $ nn (inserts (return k) (return w) vs)
                    }
              ; assignLhs (lift mvf)
              }
        }
    evalAssignRoute (T.Atom k) = assignSelf <$> evalName k
      do{ kf <- evalName k
        ; return $ \ vf ->
            do{ env <- ask
              ; (NEnv f, NVtables vs) <- liftObjF get
              ; let vs' = inserts (runReaderT kf env) (runReaderT vf env) vs
              ; liftObjF $ put (NEnv f, NVtables vs')
              }
        }
        
        
    lookupLaddress :: T.Laddress -> Eval (StateF (IOExcept Value))
    lookupLaddress (T.Lident x) =
      return $
        do{ let k = T.Ref x
          ; (NEnv f, _) <- liftObjF get
          ; mapObjR return . lift $ runReaderT (lookupF k) (CEnv f)
          --; (self, super) <- lift ask
          --; return $ runObjF (lookupEnvF k) (CEnv f) (self, super)
          }
    lookupLaddress (T.Lroute r) = lookupRoute r
       
       
    lookupRoute :: T.Route T.Laddress -> Eval (StateF (IOExcept Value))
    lookupRoute (T.Route l key) =
      do{ kf <- evalName key
        ; b <- lookupLaddress l
        ; return $
          do{ mv <- b
            ; env <- ask
            ; mapObjF return $ mapReaderT (\ kf' -> lookupValueR kf' (liftObjF mv)) kf
            --; mapObjR return . lift $ lookupValueR (runReaderT kf env) (liftObjR mv)
            --; (self, super) <- lift ask
            --; return $ runObjR (lookupValueR (runEnvF kf env) (liftObjR mv)) (self, super)
            }
        }
    lookupRoute (T.Atom key) =
      do{ kf <- evalName key
        ; return $
          do{ (_, NVtables vs) <- liftObjF get
            ; mapObjF return $
                do{ k <- kf
                  ; (self', super') <- execVtables vs
                  ; lift $
                      local
                        ((_, super) -> (self', Super $ getSuper super' `concatVtable` getSuper super))
                        (lookupR k)
                  }
            }
            {-; (self, super) <- lift ask
            ; return $
                do{ k <- runObjF kf env self super
                  ; (self', super') <- execVtables vs
                  ; runObjR (lookupVtable k) self' (Super $ getSuper super' `concatVtable` getSuper super)
                  }
            }-}
        }
evalAssign (T.Lnode xs) = 
  do{ (u, b) <- foldr (\(u, s) x -> (u <|> collectUnpackStmt x, s >> x)) (Nothing, return ()) <$> sequence (map collectReversibleStmt xs)
    ; maybe
        (return $ \ vf ->
          mapObjF (\ s -> evalState s (Rem vf)) b)
        (\l -> unpack l b)
        u
    }
  where
    collectReversibleStmt :: T.ReversibleStmt -> Eval (StateUF ())
    collectReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ getRoute <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign l
        ; unsetRoute <- unsetPlainRoute keyroute
        ; return $
            do{ Rem rf <- liftObjF get
              ; mapObjF lift $ assignLhs (getRoute rf)
              ; liftObjF put $ Rem (unset rf)
              }
              {- (Rem rf, NEnv f, NVtables vs) <- liftObjF get
              ; env <- askEnvF
              ; self <- askSelfF
              ; super <- askSuperF
              ; let (NEnv f', NVtables vs') = execState (runObjR (assignLhs (getRoute rf)) env self super) (NEnv f, NVtables vs)
              ; liftObjF $ put (Rem $ unset rf, NEnv f', NVtables vs')
             -}
        }
    collectReversibleStmt _ = return $ return ()
        
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
                  
    unpack :: T.Lval -> IOF Value -> StateUF () -> Eval (IOF Value -> StateF ())
    unpack l b = 
      do{ assignLhs <- evalAssign l
        ; return $ \ vf ->
            do{ Rem rf <- mapObjF (\s -> execState s (Rem vf)) b
              ; assignLhs rf
              }
              {-env <- askEnvF
              ; self <- askSelfF
              ; super <- askSuperF
              ; (NEnv f, NVtables vs) <- liftObjF get
              ; let (Rem rf, NEnv f', NVtables vs') <- execState (runObjR b env self super) (Rem vf, NEnv f, NVtables vs)
              ; assignLhs rf
              ; liftObjF $ put (NEnv f', NVtables vs')
              -}
        }
        
    
    viewPlainRoute :: T.PlainRoute -> Eval (Gets' (IOF Value) (IOF Value))
    viewPlainRoute (T.PlainRoute (T.Atom key)) = viewValueF <$> evalName key
    viewPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (viewValueF <$> evalName key) <*> viewPlainRoute l
        
        
    overPlainRoute :: T.PlainRoute -> Eval (Sets' (IOF Value) (IOF Value))
    overPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= overValueF
    overPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (evalName key >>= overValueF) <*> overPlainRoute l
    
    
    unsetPlainRoute :: T.PlainRoute -> Eval (IOF Value -> IOF Value)
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = unsetKey key
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> unsetKey key
        
    
    unsetKey :: T.Name T.Rval -> Eval (IOF Value -> IOF Value)
    unsetKey key =
      do{ kf <- evalName key
        ; nn <- newNode
        ; return $ \ vf ->
            do{ k <- kf
              ; v <- vf
              ; return $ nn (deletes (return k) (unNode v))
              }
        }
  
  
