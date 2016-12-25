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
  ( IOExcept
  , catchUnboundVar
  , liftIO
  , Vtable(Vtable)
  , concatVtable
  , emptyVtable
  , insertVtable
  , deleteVtable
  , lookupVtable
  , EnvF
  , emptyEnvF
  , concatEnvF
  , lookupEnvF
  , execEnvF
  , ValueF
  , KeyF
  , lookupValueF
  , Vtables'
  , execVtables'
  , emptyVtables'
  , inserts'
  , concats'
  , deletes'
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

type Gets' s a = s -> a
type Sets' s a = (a -> a) -> s -> s
  
viewValueF :: (EnvF -> KeyF) -> Gets' (EnvF -> ValueF) (EnvF -> ValueF)
viewValueF kf vf ne e v s = let e' = execEnvF ne e v s in lookupValueF (kf e') (vf e')


overValueF :: (EnvF -> KeyF) -> Eval (Sets' (EnvF -> ValueF) (EnvF -> ValueF))
overValueF kf =
  do{ nn <- newNode
    ; let over f vf ne e v s =
            do{ let e' = execEnvF ne e v s
              ; let kf' _ _ = kf e' v s
                    wf' _ _ = f (viewValueF kf vf) e' v s
              ; vs <- unNode <$> vf e' v s
              ; return $ nn (inserts' kf' wf' vs)
              }
    ; return over
    }


viewSelf :: (EnvF -> KeyF) -> EnvF -> ValueF    
viewSelf kf e v s =
  do{ k <- kf e v s
    ; (k `lookupVtable`) v s
    }

    
showVtable :: Vtable -> String
showVtable (Vtable xs) = show (map fst xs)
    
 
evalName :: T.Name T.Rval -> Eval (EnvF -> KeyF)
evalName (T.Key r) = (\ f e v s -> T.Key <$> f e v s) <$> evalRval r
evalName (T.Ref x) = return (\ _ _ _ -> return $ T.Ref x)

evalRval :: T.Rval -> Eval (EnvF -> ValueF)
evalRval (T.Number x) = return (\ _ _ _ -> return $ Number x)
evalRval (T.String x) = return (\ _ _ _ -> return $ String x)
evalRval (T.Rident x) = return (lookupEnvF (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (EnvF -> ValueF)
    evalRoute (T.Route r x) = viewValueF <$> evalName x <*> evalRval r
    evalRoute (T.Atom x) = viewSelf <$> evalName x
evalRval (T.Rnode stmts) =
  do{ let inits _ _ _ _ = (emptyEnvF, emptyVtables')
    ; fvs <- foldM collectStmt inits stmts
    ; nn <- newNode
    ; let vf e v s = return $ nn vs (emptyVtables')
            where
              (ne, vs) = fvs ne e v s
    ; return vf
    }
  where
    collectStmt :: (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> T.Stmt -> Eval (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    collectStmt fvs (T.Assign l r) = evalAssign l <*> evalRval r <*> pure fvs
    collectStmt fvs (T.Unpack r) =
      do{ vf <- evalRval r
        ; let fvs' ne e v s = (f, gg vs)
                where
                  e' = execEnvF ne e v s
                  gg vs l r =
                    do{ (v, s) <- vs l r
                      ; val <- vf e' v s
                      ; (v', s') <- execVtables' (unNode val)
                      ; return (v' `concatVtable` (s' `concatVtable` v), s)
                      }
                  (f, vs) = fvs ne e v s
        ; return fvs'
        }
    collectStmt fvs (T.Eval r) =
      do{ vf <- evalRval r
        ; let fvs' ne e v s = (f, gg vs)
                where
                  e' = execEnvF ne e v s
                  gg vs l r =
                    do{ (v, s) <- vs l r
                      ; _ <- vf e' v s
                      ; return (v, s)
                      }
                  (f, vs) = fvs ne e v s
        ; return fvs'
        }
evalRval (T.App x y) =
  do{ xf <- evalRval x
    ; yf <- evalRval y
    ; nn <- newNode
    ; let vf e v s =
            do{ xval <- xf e v s
              ; yval <- yf e v s
              ; return $ nn (unNode yval `concats'` unNode xval)
              }
    ; return vf
    }
evalRval (T.Unop sym x) =
  do{ xf <- evalRval x
    ; let vf e v s =
            do{ val <- xf e v s
              ; evalUnop sym val
              }
    ; return vf
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x =
      do{ (v, s) <- execVtables' (unNode x)
        ; (T.Key (unopSymbol sym) `lookupVtable`) v s
        }
evalRval (T.Binop sym x y) =
  do{ xf <- evalRval x
    ; yf <- evalRval y
    ; let vf e v s =
            do{ xval <- xf e v s
              ; yval <- yf e v s
              ; evalBinop sym xval yval
              }
    ; return vf
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = 
      do{ xop <- uncurry (T.Key (binopSymbol sym) `lookupVtable`) <*> execVtables' (unNode x)
        ; let kf _ _ = return $ T.Key rhsSymbol
              vf _ _ = return $ y
              vs = inserts' kf vf (unNode xop)
        ; uncurry (T.Key resultSymbol `lookupVtable`) <*> execVtables' vs
        }
        
        
evalAssign :: T.Lval -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    evalAssignLaddress (T.Lident x) = return $ assign (T.Ref x)
      where
        assign k vf fvs ne e v s = (return . (f' `concatEnvF` f), vs)
          where
            (f, vs) = fvs ne e v s
            e' = execEnvF ne e v s
            f' _ _ = Vtable [(k, vf e')]
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; lf <- lookupLaddress
        ; let assignKey kf wf fvs ne e v s = 
                do{ let e' = execEnvF ne e v s
                        kf' _ _ = kf e' v s
                        vf' _ _ = wf e' v s
                  ; ws <- lf fvs ne e v s
                  ; return $ nn (inserts' kf' vf' ws)
                  }
        ; (.) <$> evalAssignLaddress l <*> (assignKey <$> evalName x)
        }
    evalAssignRoute (T.Atom k) = assignSelf <$> evalName k
      where
        assignSelf kf vf fvs ne e v s = (return . setEnv k, inserts' (kf e') (vf e') vs)
          where
            e' = execEnvF ne e v s
            (f, vs) = fvs ne e v s
        setEnv (T.Key _) _ _ = emptyVtable
        setEnv (T.Ref x) v s = let vf' _ _ = (T.Ref x `lookupVtable`) v s in Vtable [(T.Ref x, vf')]
        
        
    lookupLaddress :: T.Laddress -> Eval ((EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> Vtables')
    lookupLaddress (T.Lident x) = return $ lookup (T.Ref x)
      where
        lookup k fvs ne e v s =
          do{ let (f, _) = fvs ne e v s
            ; (unNode <$> lookupEnvF k (f `concatEnvF` e) v s)
              `catchUnboundVar`
                return emptyVtables'
            }
    lookupLaddress (T.Lroute r) = lookupRoute r
       
       
    lookupRoute :: T.Route T.Laddress -> Eval ((EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> Vtables')
    lookupRoute (T.Route l key) = viewValueF <$> evalName key <*> lookupLaddress l
    lookupRoute (T.Atom key) = lookup <$> evalName key
      where
        lookup kf fvs ne e v s =
          do{ let (_, vs) = fvs ne e v s
                  e' = execEnvF ne e v s
            ; k <- kf e' v s
            ; (v', s') <- execVtables' vs
            ; (unNode <$> lookupVtable k v' (s' `concatVtable` s))
              `catchUnboundVar`
                return emptyVtables'
            }
evalAssign (T.Lnode xs) = 
  do{ let inits vf = (vf, inits')
          inits' _ _ _ = (emptyEnvF, emptyVtables')
    ; (u, rfvs) <- foldM (\(u, s) x -> (,) <$> pure (collectUnpackStmt u x) <*>  collectReversibleStmt s x) (Nothing, inits') xs
    ; maybe
        (return $ snd . rfvs)
        (\l -> unpack l rfvs)
        u
    }
  where
    collectReversibleStmt :: ((EnvF -> ValueF) -> (EnvF -> ValueF, EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))) -> T.ReversibleStmt -> Eval ((EnvF -> ValueF) -> (EnvF -> ValueF, EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')))
    collectReversibleStmt rfvs (T.ReversibleAssign keyroute l) =
      do{ get <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign l
        ; unset <- unsetPlainRoute keyroute
        ; let rfvs' vf = (unset rf, assignLhs (get rf) vf)
                where
                  (rf, fvs) = rfvs vf
        ; return rfvs'
        }
    collectReversibleStmt rfvs _ = return rfvs
        
    
    collectUnpackStmt :: Maybe T.Lval -> T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt Nothing (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt x _ = x
                  
    unpack :: T.Lval -> ((EnvF -> ValueF) -> (EnvF -> ValueF,  EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))) -> Eval ((EnvF -> ValueF) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    unpack l rfvs =
      do{ nn <- newNode
        ; (.) <$> uncurry (evalAssign l) <*> rfvs
        }
        
    
    viewPlainRoute :: T.PlainRoute -> Eval (Gets' (EnvF -> ValueF) (EnvF -> ValueF))
    viewPlainRoute (T.PlainRoute (T.Atom key)) = viewValueF <$> evalName key
    viewPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (viewValueF <$> evalName key) <*> viewPlainRoute l
        
        
    overPlainRoute :: T.PlainRoute -> Eval (Sets' (EnvF -> ValueF) (EnvF -> ValueF))
    overPlainRoute (T.PlainRoute (T.Atom key)) = evalName key >>= overValueF
    overPlainRoute (T.PlainRoute (T.Route l key)) =
      (.) <$> (evalName key >>= overValueF) <*> overPlainRoute l
    
    
    unsetPlainRoute :: T.PlainRoute -> Eval ((EnvF -> ValueF) -> (EnvF -> ValueF))
    unsetPlainRoute (T.PlainRoute (T.Atom key)) = unsetKey key
    unsetPlainRoute (T.PlainRoute (T.Route l key)) = overPlainRoute l <*> unsetKey key
        
    
    unsetKey :: T.Name T.Rval -> Eval ((EnvF -> ValueF) -> EnvF -> ValueF)
    unsetKey key =
      do{ nn <- newNode
        ; let deleteKey kf vf e v s =
                do{ let kf' _ _ = kf e v s
                  ; val <- vf e v s
                  ; return $ nn (deletes' kf' (unNode val))
                  }
        ; deleteKey <$> evalName key
        }
  
  
