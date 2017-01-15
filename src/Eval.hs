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
viewValue k vf = liftScoped . lookupVtable k . unNode =<< vf


overValue :: T.Name Value -> Eval (Sets' (Scoped IOClassed Value) (Scoped IOClassed Value))
overValue k =
  do{ nn <- newNode
    ; return $ \ f vf ->
        do{ xs <- unNode <$> vf
          ; w <- f . liftScoped $ lookupVtable k xs
          ; return . nn $ insertVtable k (return w) xs
          }
    }

    
unsetValue :: T.Name Value -> Eval (Scoped IOClassed Value -> Scoped IOClassed Value)
unsetValue k =
  do{ nn <- newNode
    ; return $ \vf ->
        do{ xs <- unNode <$> vf
          ; return . nn $ deleteVtable k xs
          }
    }


viewSelf :: T.Name Value -> Scoped IOClassed Value
viewSelf k = liftScoped (lookupVtable k =<< askClassed)


evalName :: T.Name T.Rval -> Eval (T.Name Value)
--evalName (T.Key r) = (T.Key <$>) <$> evalRval r
evalName (T.Ref x) = return $ T.Ref x


evalRval :: T.Rval -> Eval (Scoped IOClassed Value)
evalRval (T.Number x) = return . return $ Number x
evalRval (T.String x) = return . return $ String x
evalRval (T.Rident x) = return (lookupEnv x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (Scoped IOClassed Value)
    evalRoute (T.Route r x) =
      do{ k <- evalName x
        ; vf <- evalRval
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
        do{ self <- askScoped
          ; let par = bindClassed self
          ; return . nn $ \ super -> self
              where
                scope = (par, super) 
                (env, self) = runIdentity . runScoped (b $ return scope) $ env
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
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = T.Key (unopSymbol sym) `lookupVtable` unNode x
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
      do{ xop <- T.Key (binopSymbol sym) `lookupVtable` unNode x
        ; let vsop = insertVtable (T.Key rhsSymbol) (return y) (unNode xop)
        ; T.Key resultSymbol `lookupVtable` vsop
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

       
       
evalStmt :: T.Stmt -> Eval (Scoped' Scope -> Scoped' Scope))
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Eval (Scoped IOClassed Scope -> Scoped IOClassed Scope))
    evalUnassign (T.Lident x) = return (over_1 (deleteVtable (T.Ref x) <$>) <$>)
    evalUnassign (T.Lroute x) = evalUnassignRoute x
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Eval (Scoped' Scope -> Scoped' Scope))
    evalUnassignRoute (T.Route l x) =
      do{ nn <- newNode
        ; vf <- evalLaddr l
        ; k <- evalName x
        ; evalAssign (T.Laddress l) <*> pure
            (do{ xs <- catchUnboundVar (unNode <$> vf) id
               ; return . nn $ deleteVtable k . xs
               })
        }
    evalUnassignRoute (T.Atom x) =
      do{ k <- evalName x
        ; return (over_2 . deleteVtable k <$>)
        }
evalStmt (T.Assign l r) = evalAssign l <*> evalRval r
evalStmt (T.Unpack r) =
  do{ vf <- evalRval r
    ; return ( (over_2  . concatVtable <$> (unNode <$> vf <*> emptyVtable)) <*> )
    }
evalStmt (T.Eval r) = evalRval r >> return id


evalAssign :: T.Lval -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope))
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope)
    evalAssignLaddress (T.Lident x) =
      return $ \ vf ->
        do{ let k = T.Ref x
          ; vr <- mapScoped return vf
          ; (over_1 (insertVtable k vr <$>) <$>)
          }
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval (Scoped IOClassed Value -> Scoped' Scope -> Scoped' Scope))
    evalAssignRoute (T.Route l key) =
      do{ nn <- newNode
        ; vf <- evalLaddr l
        ; k <- evalName key
        ; assignLhs <- evalAssignLaddress l
        ; return $ \ wf sc ->
            do{ env <- askScoped
              ; let wr = runScoped wf env
              ; (env', self') <- sc
              ; xs <- local (const env') . mapScoped (local (const self')) $ catchUnboundVar (unNode <$> vf) (return id)
              ; assignLhs (return . nn $ insertVtable k wr . xs) sc
              }
        }
    evalAssignRoute (T.Atom key) =
      do{ k <- evalName key
        ; return $ \ vf ->
            do{ vr <- mapScoped return vf
              ; (over_2 (insertVtable k vr) <$>)
              }
        }
evalAssign (T.Lnode xs) = 
  do{ (u, b) <- foldr (over_1 (flip (<|>)) . over_2 (.)) (Nothing, id) <$> mapM (\ x -> (,) <$> pure (collectUnpackStmt x) <*> evalReversibleStmt x) xs
    ; maybe
        (return $ \ vf sf -> get_1 <$> b ((,) <$> sf <*> vf))
        (\l -> unpackLval l b)
        u
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> Eval (Scoped' Unpack -> Scoped' Unpack)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ assignRem <- (.) <$> evalAssign l <*> viewPlainRoute keyroute
        ; unsetRem <- unsetPlainRoute keyroute
        ; return $ \ sf ->
            do{ (scope, rem) <- sf
              ; scope' <- assignRem (liftScoped rem) (liftScoped . Identity scope)
              ; rem' <- unsetRem (liftScoped rem)
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
          do{ (scope', rem') <- b <$> ((,) <$> sf <*> vf)
            ; assignLhs rem' scope
            })
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
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = unsetValue key
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> unsetValue key
        