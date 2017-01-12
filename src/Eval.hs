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

newtype Rem = Rem { getRem :: IOClassed Value }


  
viewValue :: Scoped IOClassed (T.Name Value) -> Gets' (Scoped IOClassed Value) (Scoped IOClassed Value)
viewValue kf vf =
  do{ k <- kf
    ; v <- vf
    ; liftScoped $ lookupClasses k (unNode v)
    }


overValue :: Scoped IOClassed (T.Name Value) -> Eval (Sets' (Scoped IOClassed Value) (Scoped IOClassed Value))
overValue kf =
  do{ nn <- newNode
    ; return $ \ f vf ->
        do{ k <- kf
          ; v <- vf
          ; w <- f . liftScoped $ lookupClasses k (unNode v)
          ; return $ nn (inserts (return k) (return w) `concats` unNode v)
          }
    }

    
unsetValue :: Scoped IOClassed (T.Name Value) -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
unsetValue kf =
  do{ nn <- newNode
    ; return $ \ vf ->
        do{ k <- kf
          ; v <- vf
          ; return $ nn (deletes (return k) `concats` unNode v)
          }
    }


viewSelf :: Scoped IOClassed (T.Name Value) -> Scoped IOClassed Value
viewSelf kf = kf >>= liftScoped . lookupSelf


viewScopes :: T.Laddress -> Eval (Gets' Scopes (Scoped IOClassed Value))
evalLaddr (T.Lident x) = return $
  do{ 
  (lookupEnv (T.Ref x))
evalLaddr (T.Lroute r) = lookupRouteB r
  where
    lookupRouteB :: T.Route T.Laddress -> Eval (Scoped IOClassed Value)
    lookupRouteB (T.Route l key) = viewValue <$> evalName key <*> evalLaddr l
    lookupRouteB (T.Atom key) =
      do{ kf <- evalName key
        ; return $
          do{ NScope vs <- liftScoped get
            ; mapScoped return $
                do{ k <- kf
                  ; scope <- liftScoped $ execClasses vs
                  ; lift $
                      local
                        (const scope)
                        (lookupSelf k)
                  }
            }
        }

 
evalName :: T.Name T.Rval -> Eval (Scoped IOClassed (T.Name Value))
evalName (T.Key r) = (T.Key <$>) <$> evalRval r
evalName (T.Ref x) = return . return $ T.Ref x


evalRval :: T.Rval -> Eval (Scoped IOClassed Value)
evalRval (T.Number x) = return . return $ Number x
evalRval (T.String x) = return . return $ String x
evalRval (T.Rident x) = return (lookupEnv (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (Scoped IOClassed Value)
    evalRoute (T.Route r x) = viewValue <$> evalName x <*> evalRval r
    evalRoute (T.Atom x) = viewSelf <$> evalName x
evalRval (T.Rnode []) = return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ b <- sequence_ <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return $
        do{ scope <- askScoped
          ; Env par <- lift ef
          ; par' <- lift . bindObjR . return $ par
          ; let (NEnv nf, NSelf vs) =
                  execState
                    (runObjF b (Env <$> nf) selfs)
                    (NEnv . return $ par', NSelf emptyClasses)
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
          ; liftScoped $ evalUnop sym v
          }
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupClasses` unNode x
evalRval (T.Binop sym x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; return $
        do{ v <- vf
          ; w <- wf
          ; liftScoped $ evalBinop sym v w
          }
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xop <- T.Key (binopSymbol sym) `lookupClasses` unNode x
        ; let vsop = inserts (return $ T.Key rhsSymbol) (return y) (unNode xop)
        ; T.Key resultSymbol `lookupClasses` vsop
        }
evalRval (T.Import x) = evalRval x
       
       
evalStmt :: T.Stmt -> Eval (ScopedB ())
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (ScopedB ())
    evalUnassign (T.Lident x) =
      return $
        do{ let k = T.Ref x
          ; liftScoped $
              do{ NScope vs <- get
                ; let vs' = deletes (return k) vs
                ; put $ NScope vs'
                }
          }
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (ScopedB ())
    evalUnassignRoute (T.Route l x) =
      do{ nn <- newNode
        ; getLaddr <- lookupB l
        ; assignLaddr <- evalAssign (T.Laddress l)
        ; kf <- evalName x
        ; unsetLaddr <- unsetValue kf
        ; return $
            do{ mv <- getLaddr
              ; assignLaddr (unsetLaddr (liftScoped mv))
              }
        }
    evalUnassignRoute (T.Atom x) =
      do{ kf <- evalName x
        ; return $
            do{ scope <- askScoped
              ; liftObjF $
                  do{ NScope vs <- get
                    ; let vs' = deletes kf vs
                    ; put $ NScope vs'
                    }
              }
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
evalStmt (T.Unpack r) = mapObjF unpack <$> evalRval r
  where
    unpack :: IOExcept Value -> Build ()
    unpack mv =
      do{ NScope vs <- get 
        ; let vs' = mv `unpacks` vs
        ; put $ NScope vs'
        }
evalStmt (T.Eval r) = mapScoped (\ _ -> return ()) <$> evalRval r
        
       
evalAssign :: T.Lval -> Eval (Scoped IOClassed Value -> ScopedB ())
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (Scoped IOClassed Value -> ScopedB ())
    evalAssignLaddress (T.Lident x) =
      return $ \ vf ->
        do{ let k = T.Ref x
          ; scope <- askScoped
          ; liftScoped $
              do{ NScope vs <- get
                ; let vs' = insertsEnv (return k) vf vs
                ; put $ NScope vs'
                }
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (Scoped IOClassed Value -> ScopedB ())
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; getLaddr <- lookupB l
        ; assignLaddr <- evalAssignLaddress l
        ; kf <- evalName x
        ; return $ \wf ->
            do{ mv <- getLaddr
              ; let mvf =
                      do{ k <- kf
                        ; w <- wf
                        ; vs <- liftScoped $ catchUnboundVar (unNode <$> mv) (return emptyClasses)
                        ; return $ nn (insertsSelf (return k) (return w) vs)
                        }
              ; assignLaddr mvf
              }
        }
    evalAssignRoute (T.Atom k) =
      do{ kf <- evalName k
        ; return $ \ vf ->
            do{ scope <- askScoped
              ; liftScoped $
                  do{ NScope vs <- get
                  ; let vs' = insertsSelf kf vf vs
                  ; put $ NScope vs'
                  }
              }
        }
evalAssign (T.Lnode xs) = 
  do{ (u, b) <- foldr (\ (u', s') (u, s) -> (u <|> u', s' >> s)) (Nothing, return ()) <$> mapM (\ x -> (,) <$> pure (collectUnpackStmt x) <*> evalReversibleStmt x) xs
    ; maybe
        (return $ \ vf ->
          mapScoped (\ s -> evalStateT s (Rem vf)) b)
        (\l -> unpackLval l b)
        u
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (ScopedUB ())
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ getRem <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign l
        ; unsetRem <- unsetPlainRoute keyroute
        ; return $
            do{ Rem rf <- liftScoped get
              ; mapScoped lift $ assignLhs (getRem rf)
              ; liftScoped . put $ Rem (unsetRem rf)
              }
        }
    evalReversibleStmt _ = return $ return ()
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> ScopedUB () -> Eval (Scoped IOClassed Value -> ScopedB ())
    unpackLval l b = 
      do{ assignLhs <- evalAssign l
        ; return $ \ vf ->
            do{ Rem rf <- mapScoped (\s -> execStateT s (Rem vf)) b
              ; assignLhs rf
              }
        }
        
    
    viewPlainRoute :: T.PlainRoute -> Eval (Gets' (Scoped IOClassed Value) (Scoped IOClassed Value))
    viewPlainRoute (T.PlainRoute (T.Atom key)) = viewValue <$> evalName key
    viewPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (viewValue <$> evalName key) <*> viewPlainRoute l
        
        
    overPlainRoute :: T.PlainRoute -> Eval (Sets' (Scoped IOClassed Value) (Scoped IOClassed Value))
    overPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= overValue
    overPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (evalName key >>= overValue) <*> overPlainRoute l
    
    
    unsetPlainRoute :: T.PlainRoute -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = unsetValue key
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> unsetValue key
        