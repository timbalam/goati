module Eval
  ( evalRval
  )
where
import Control.Monad.Except
  ( throwError
  , catchError
  )
import Control.Monad.Trans.State
  ( StateT
  , evalStateT
  , execStateT
  , State
  , evalState
  , execState
  , get
  , put
  )
import Control.Monad.Trans.Reader
  ( ReaderT
  , runReaderT
  , mapReaderT
  , ask
  , local
  )
import Control.Monad.Trans.Class( lift )
import Control.Applicative( (<|>) )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Gets' s a = s -> a
type Sets' s a = (a -> a) -> s -> s
newtype NEnv = NEnv { getNEnv :: IOR Vtable }
newtype NVtables = NVtables { getNVtables :: Vtables }
type Build = State (NEnv, NVtables)
type BuildF = ObjF Build
newtype Rem = Rem { getRem :: IOF Value }
type BuildUF = ObjF (StateT Rem Build)
  
  
viewValueF :: IOF (T.Name Value) -> Gets' (IOF Value) (IOF Value)
viewValueF kf vf =
  do{ k <- kf
    ; v <- vf
    ; liftObjF $ lookupVtables k (unNode v)
    }


overValueF :: IOF (T.Name Value) -> Eval (Sets' (IOF Value) (IOF Value))
overValueF kf =
  do{ nn <- newNode
    ; return $ \ f vf ->
        do{ k <- kf
          ; v <- vf
          ; w <- f . liftObjF $ lookupVtables k (unNode v)
          ; return $ nn (inserts (return k) (return w) (unNode v))
          }
    }

    
unsetValueF :: T.Name T.Rval -> Eval (IOF Value -> IOF Value)
unsetValueF key =
  do{ kf <- evalName key
    ; nn <- newNode
    ; return $ \ vf ->
        do{ k <- kf
          ; v <- vf
          ; return $ nn (deletes (return k) (unNode v))
          }
    }


viewSelfF :: IOF (T.Name Value) -> IOF Value
viewSelfF kf = kf >>= lift . lookupR


lookupB :: T.Laddress -> Eval (BuildF (IOExcept Value))
lookupB (T.Lident x) =
  return $
    do{ let k = T.Ref x
      ; (NEnv f, _) <- liftObjF get
      ; lift . mapObjR return $ runReaderT (lookupF k) (CEnv f)
      }
lookupB (T.Lroute r) = lookupRouteB r
  where
    lookupRouteB :: T.Route T.Laddress -> Eval (BuildF (IOExcept Value))
    lookupRouteB (T.Route l key) =
      do{ kf <- evalName key
        ; bv <- lookupB l
        ; return $
            do{ mv <- bv
              ; let vf' = liftObjR mv
              ; mapObjF return $ mapReaderT (\ kf' -> lookupValueR kf' vf') kf
              }
        }
    lookupRouteB (T.Atom key) =
      do{ kf <- evalName key
        ; return $
          do{ (_, NVtables vs) <- liftObjF get
            ; mapObjF return $
                do{ k <- kf
                  ; (self', super') <- liftObjF $ execVtables vs
                  ; lift $
                      local
                        (\ (_, super) -> (self', Super $ getSuper super' `concatVtable` getSuper super))
                        (lookupR k)
                  }
            }
        }

 
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
evalRval (T.Rnode []) = return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ b <- sequence_ <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return $
        do{ (CEnv env, PEnv par) <- askEnvF
          ; (self, super) <- askObjF
          ; par' <- lift $ bindObjR (concatVtable <$> pure (getSelf self) <*> env)
          ; let (NEnv f, NVtables vs) = execState (runObjF b (CEnv f, PEnv par `concatVtable` par') (self, super)) (NEnv $ return emptyVtables, NVtables emptyVtables)
          ; return $ nn vs
          }
    }
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
          ; liftObjF $ evalUnop sym v
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
          ; liftObjF $ evalBinop sym v w
          }
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xop <- T.Key (binopSymbol sym) `lookupVtables` unNode x
        ; let vsop = inserts (return $ T.Key rhsSymbol) (return y) (unNode xop)
        ; T.Key resultSymbol `lookupVtables` vsop
        }
evalRval (T.Import x) = evalRval x
       
       
evalStmt :: T.Stmt -> Eval (BuildF ())
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (BuildF ())
    evalUnassign (T.Lident x) =
          return $
            do{ let k = T.Ref x
              ; liftObjF $
                  do{ (NEnv f, NVtables vs) <- get
                    ; let f' = deleteVtable k <$> f
                          vs' = deletes (return k) vs
                    ; put (NEnv f', NVtables vs')
                    }
              }
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (BuildF ())
    evalUnassignRoute (T.Route l x) =
      do{ nn <- newNode
        ; b <- lookupB l
        ; assignLhs <- evalAssign (T.Laddress l)
        ; unsetKey <- unsetValueF x
        ; return $
            do{ mv <- b
              ; assignLhs (unsetKey (liftObjF mv))
              }
        }
    evalUnassignRoute (T.Atom x) =
      do{ kf <- evalName x
        ; return $
            do{ envs <- askEnvF
              ; mk <- mapObjF return kf
              ; liftObjF $
                  do{ (NEnv f, NVtables vs) <- get
                    ; let f' = deleteVtable <$> liftObjR mk <*> f
                          vs' = deletes (runReaderT kf envs) vs
                    ; put (NEnv f', NVtables vs')
                    }
              }
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
evalStmt (T.Unpack r) = mapObjF unpack <$> evalRval r
  where
    unpack :: IOExcept Value -> Build ()
    unpack mv =
      do{ (NEnv f, NVtables vs) <- get 
        ; let vs' = mv `unpacks` vs
        ; put (NEnv f, NVtables vs')
        }
evalStmt (T.Eval r) = mapObjF (\ _ -> return ()) <$> evalRval r
        
       
evalAssign :: T.Lval -> Eval (IOF Value -> BuildF ())
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (IOF Value -> BuildF ())
    evalAssignLaddress (T.Lident x) =
      return $ \ vf ->
        do{ let k = T.Ref x
          ; envs <- askEnvF
          ; liftObjF $
              do{ (NEnv f, NVtables vs) <- get
                ; let f' = insertVtable k (runReaderT vf envs) <$> f
                ; put (NEnv f', NVtables vs)
                }
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (IOF Value -> BuildF ())
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; b <- lookupB l
        ; assignLhs <- evalAssignLaddress l
        ; kf <- evalName x
        ; return $ \wf ->
            do{ mv <- b
              ; let mvf =
                      do{ k <- kf
                        ; w <- wf
                        ; vs <- liftObjF $ catchUnboundVar (unNode <$> mv) (return emptyVtables)
                        ; return $ nn (inserts (return k) (return w) vs)
                        }
              ; assignLhs mvf
              }
        }
    evalAssignRoute (T.Atom k) =
      do{ kf <- evalName k
        ; return $ \ vf ->
            do{ envs <- askEnvF
              ; liftObjF $
                  do{ (NEnv f, NVtables vs) <- get
                  ; let vs' = inserts (runReaderT kf envs) (runReaderT vf envs) vs
                  ; put (NEnv f, NVtables vs')
                  }
              }
        }
evalAssign (T.Lnode xs) = 
  do{ (u, b) <- foldr (\ (u', s') (u, s) -> (u <|> u', s' >> s)) (Nothing, return ()) <$> mapM (\ x -> (,) <$> pure (collectUnpackStmt x) <*> evalReversibleStmt x) xs
    ; maybe
        (return $ \ vf ->
          mapObjF (\ s -> evalStateT s (Rem vf)) b)
        (\l -> unpackLval l b)
        u
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (BuildUF ())
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ getRoute <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign l
        ; unsetRoute <- unsetPlainRoute keyroute
        ; return $
            do{ Rem rf <- liftObjF get
              ; mapObjF lift $ assignLhs (getRoute rf)
              ; liftObjF . put $ Rem (unsetRoute rf)
              }
        }
    evalReversibleStmt _ = return $ return ()
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> BuildUF () -> Eval (IOF Value -> BuildF ())
    unpackLval l b = 
      do{ assignLhs <- evalAssign l
        ; return $ \ vf ->
            do{ Rem rf <- mapObjF (\s -> execStateT s (Rem vf)) b
              ; assignLhs rf
              }
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
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = unsetValueF key
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> unsetValueF key
        