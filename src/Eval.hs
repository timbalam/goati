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
import Control.Monad.Identity
  ( Identity(Identity)
  , runIdentity
  )
import Control.Monad.Trans.Class( lift )
import Control.Applicative( (<|>) )
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Gets' s a = s -> a
type Sets' s a = (a -> a) -> s -> s
type Scope = (Env, Self)
type Rem = IOClassed Value
type Unpack = (Scope, Rem)


view_1 :: Gets' (a, b) a
view_1 = fst


over_1 :: Sets' (a, b) a
over_1 f (a, b) = (f a, b)


view_2 :: Gets' (a, b) b
view_2 = snd

over_2 :: Sets' (a, b) b
over_2 f (a, b) = (a, f b) 

  
viewValue :: T.Name Value -> Gets' (Scoped IOClassed Value) (Scoped IOClassed Value)
viewValue k vf =
  do{ xs <- unNode <$> vf
    ; let self = xs emptyVtable
    ; liftScoped . local (const self) . lookupVtable k $ self
    }


overValue :: T.Name Value -> Eval (Sets' (Scoped IOClassed Value) (Scoped IOClassed Value))
overValue k =
  do{ nn <- newNode
    ; return $ \ f vf ->
        do{ xs <- unNode <$> vf
          ; env <- askScoped
          ; let node super = self'
                  where
                    self = xs super
                    w = f . liftScoped . local (const self) . lookupVtable k $ self
                    self' = insertVtable k (runScoped w env) self
          ; return . nn $ node
          }
    }

    
unsetValue :: T.Name Value -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
unsetValue k =
  do{ nn <- newNode
    ; return $ \vf ->
        do{ xs <- unNode <$> vf
          ; return . nn $ deleteVtable k . xs
          }
    }


viewSelf :: T.Name Value -> Scoped IOClassed Value
viewSelf k = liftScoped (lookupSelf k)


evalName :: T.Name T.Rval -> Eval (T.Name Value)
--evalName (T.Key r) = (T.Key <$>) <$> evalRval r
evalName (T.Ref x) = return $ T.Ref x


evalRval :: T.Rval -> Eval (Scoped IOClassed Value)
evalRval (T.Number x) = return . return $ Number x
evalRval (T.String x) = return . return $ String x
evalRval (T.Rident x) = return (lookupEnv (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (Scoped IOClassed Value)
    evalRoute (T.Route r x) =
      do{ k <- evalName x
        ; vf <- evalRval r
        ; return $ viewValue k vf
        }
    evalRoute (T.Atom x) =
      do{ k <- evalName x
        ; return $ viewSelf k
        }
evalRval (T.Rnode []) = return <$> newSymbol
evalRval (T.Rnode stmts) =
  do{ b <- foldr (.) id <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return $
        do{ env <- askScoped
          ; self <- liftScoped askClassed
          ; let par = local (const self) $ bindClassed env
                node super = self'
                  where
                    scope = (par, super) 
                    (env, self') = runIdentity . runScoped (b $ return scope) $ env'
                    env' = concatVtable <$> withSelf self' <*> env
          ; return . nn $ node
          }
    }
evalRval (T.App x y) =
  do{ vf <- evalRval x
    ; wf <- evalRval y
    ; nn <- newNode
    ; return $ 
        do{ v <- vf
          ; w <- wf
          ; return . nn $ unNode w . unNode v
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
    evalUnop :: T.Unop -> Value -> IOClassed Value
    evalUnop sym (Number x) = liftClassed $ primitiveNumberUnop sym x
    evalUnop sym (Bool x) = liftClassed $ primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupVtable` unNode x emptyVtable
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
    evalBinop :: T.Binop -> Value -> Value -> IOClassed Value
    evalBinop sym (Number x) (Number y) = liftClassed $ primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = liftClassed $ primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xop <- T.Key (binopSymbol sym) `lookupVtable` unNode x emptyVtable
        ; let vsop = insertVtable (T.Key rhsSymbol) (return y) . unNode xop
        ; T.Key resultSymbol `lookupVtable` vsop emptyVtable
        }
evalRval (T.Import x) = evalRval x


evalLaddr :: T.Laddress -> Eval (Scoped IOClassed Value)
evalLaddr (T.Lident x) = return (lookupEnv (T.Ref x))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Eval (Scoped IOClassed Value)
    evalLroute (T.Route l key) =
      do{ k <- evalName key
        ; vf <- evalLaddr l
        ; return $ viewValue k vf
        }
    evalLroute (T.Atom key) =
      do{ k <- evalName key
        ; return $ viewSelf k
        }

       
       
evalStmt :: T.Stmt -> Eval (Scoped' Scope -> Scoped' Scope)
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (Scoped' Scope -> Scoped' Scope)
    evalUnassign (T.Lident x) = return (over_1 (deleteVtable (T.Ref x) <$>) <$>)
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (Scoped' Scope -> Scoped' Scope)
    evalUnassignRoute (T.Route l x) =
      do{ nn <- newNode
        ; vf <- evalLaddr l
        ; k <- evalName x
        ; evalAssign (T.Laddress l) <*> pure
            (do{ mv <- mapScoped (mapClassed return) vf
               ; let mxs = catchUnboundVar (unNode <$> mv) (pure id)
               ; liftScoped . liftClassed $ (nn . (deleteVtable k .)) <$> mxs
               })
        }
    evalUnassignRoute (T.Atom x) =
      do{ k <- evalName x
        ; return (over_2 (deleteVtable k) <$>)
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
{-evalStmt (T.Unpack r) =
  do{ vf <- evalRval r
    ; return ( (over_2  . concatVtable <$> (unNode <$> vf <*> pure emptyVtable)) <*> )
    -}
evalStmt (T.Eval r) = evalRval r >> return id


evalAssign :: T.Lval -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
    evalAssignLaddress (T.Lident x) =
      return $ \ vf sf ->
        do{ let k = T.Ref x
          ; vr <- mapScoped return vf
          ; over_1 (insertVtable k vr <$>) <$> sf
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
    evalAssignRoute (T.Route l key) =
      do{ nn <- newNode
        ; vf <- evalLaddr l
        ; k <- evalName key
        ; assignLhs <- evalAssignLaddress l
        ; return $ \ wf sf ->
            do{ env <- askScoped
              ; let wr = runScoped wf env
              ; (env', self') <- sf
              ; let mv = (runClassed . runScoped vf) env' self'
                    mxs = catchUnboundVar (unNode <$> mv) (return id)
                    vf' = liftScoped . liftClassed $ nn . (insertVtable k wr .) <$> mxs
              ; assignLhs vf' sf
              }
        }
    evalAssignRoute (T.Atom key) =
      do{ k <- evalName key
        ; return $ \ vf sf ->
            do{ vr <- mapScoped return vf
              ; over_2 (insertVtable k vr) <$> sf
              }
        }
evalAssign (T.Lnode xs) = 
  do{ b <- foldr (.) id <$> mapM evalReversibleStmt xs
    ; maybe
        (return $ \ vf sf -> view_1 <$> b ((,) <$> sf <*> mapScoped pure vf))
        (\l -> unpackLval l b)
        (foldr (<|>) Nothing (map collectUnpackStmt xs))
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (Scoped' Unpack -> Scoped' Unpack)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ assignRem <- (.) <$> evalAssign l <*> viewPlainRoute keyroute
        ; unsetRem <- unsetPlainRoute keyroute
        ; return $ \ sf ->
            do{ (scope, rem) <- sf
              ; scope' <- assignRem (liftScoped rem) (return scope)
              ; rem'  <- mapScoped return . unsetRem $ liftScoped rem
              ; return (scope', rem')
              }
        }
    evalReversibleStmt _ = return id
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    unpackLval :: T.Lval -> (Scoped' Unpack -> Scoped' Unpack) -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
    unpackLval l b = 
      do{ assignLhs <- evalAssign l
        ; return $ \ vf sf ->
          do{ (scope', rem') <- b ((,) <$> sf <*> mapScoped pure vf)
            ; assignLhs (liftScoped rem') (return scope')
            }
        }
        
    
    viewPlainRoute :: T.PlainRoute -> Eval (Gets' (Scoped IOClassed Value) (Scoped IOClassed Value))
    viewPlainRoute (T.PlainRoute (T.Atom key)) = 
      do{ k <- evalName key
        ; return $ viewValue k
        }
    viewPlainRoute (T.PlainRoute (T.Route l key)) =
      do{ k <- evalName key
        ; (.) <$> pure (viewValue k) <*> viewPlainRoute l
        }
        
    overPlainRoute :: T.PlainRoute -> Eval (Sets' (Scoped IOClassed Value) (Scoped IOClassed Value))
    overPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= overValue
    overPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (evalName key >>= overValue) <*> overPlainRoute l
    
    
    unsetPlainRoute :: T.PlainRoute -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= unsetValue
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> (evalName key >>= unsetValue)
        