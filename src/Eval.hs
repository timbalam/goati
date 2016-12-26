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
viewValueF kf vf e = lookupValueF (kf e) (vf e)


overValueF :: (EnvF -> KeyF) -> Eval (Sets' (EnvF -> ValueF) (EnvF -> ValueF))
overValueF kf =
  do{ nn <- newNode
    ; let over f vf e v s =
            do{ let kf' _ _ = kf e v s
                    wf' _ _ = f (viewValueF kf vf) e v s
              ; vs <- unNode <$> vf e v s
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
evalName (T.Key r) = (\ vf e v s -> T.Key <$> vf e v s) <$> evalRval r
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
    ; let vf e v s = return $ nn vs
            where
              (ne, vs) = fvs ne' e v s
              ne' v s = concatVtable <$> pure v <*> ne v s
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
                  (f, vs) = fvs ne e v s
                  gg vs l r =
                    do{ (v, s) <- vs l r
                      ; val <- vf e' v s
                      ; (v', s') <- execVtables' (unNode val)
                      ; return (v' `concatVtable` (s' `concatVtable` v), s)
                      }
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
      do{ xop <- execVtables' (unNode x) >>= uncurry (T.Key (binopSymbol sym) `lookupVtable`)
        ; let kf _ _ = return $ T.Key rhsSymbol
              vf _ _ = return $ y
              vs = inserts' kf vf (unNode xop)
        ; execVtables' vs >>= uncurry (T.Key resultSymbol `lookupVtable`)
        }
        
        
evalAssign :: T.Lval -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    evalAssignLaddress (T.Lident x) = return $ assign (T.Ref x)
      where
        assign k vf fvs ne e v s = (f' `concatEnvF` f, vs)
          where
            (f, vs) = fvs ne e v s
            e' = execEnvF ne e v s
            f' _ _ = return $ Vtable [(k, vf e')]
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; lf <- lookupLaddress l
        ; assignLhs <- evalAssignLaddress l
        ; let assign :: (EnvF -> KeyF) -> (EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')
              assign kf wf fvs ne e v s = assignLhs vf fvs ne e v s
                where
                  e' = execEnvF ne e v s
                  kf' _ _ = kf e' v s
                  wf' _ _ = wf e' v s
                  vf _ _ _ =
                    do{ ws <- catchUnboundVar (unNode <$> lf fvs ne e v s) (return emptyVtables')
                      ; return $ nn (inserts' kf' wf' ws)
                      }
        ; assign <$> evalName x
        }
    evalAssignRoute (T.Atom k) = assignSelf <$> evalName k
      where
        assignSelf kf vf fvs ne e v s = (f, inserts' (kf e') (vf e') vs)
          where
            e' = execEnvF ne e v s
            (f, vs) = fvs ne e v s
        setEnv (T.Key _) _ _ = return emptyVtable
        setEnv (T.Ref x) v s = let vf' _ _ = (T.Ref x `lookupVtable`) v s in return $ Vtable [(T.Ref x, vf')]
        
        
    lookupLaddress :: T.Laddress -> Eval ((EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> ValueF)
    lookupLaddress (T.Lident x) = return $ lookup (T.Ref x)
      where
        lookup k fvs ne e v s =
          do{ let (f, _) = fvs ne e v s
            ; lookupEnvF k (f `concatEnvF` e) v s
            }
    lookupLaddress (T.Lroute r) = lookupRoute r
       
       
    lookupRoute :: T.Route T.Laddress -> Eval ((EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> ValueF)
    lookupRoute (T.Route l key) = (.) <$> (lookup <$> evalName key) <*> lookupLaddress l
      where
        lookup kf lf ne e v s = lookupValueF (kf e') vf v s
          where
            e' = execEnvF ne e v s
            vf _ _ = lf ne e v s
    lookupRoute (T.Atom key) = lookup <$> evalName key
      where
        lookup kf fvs ne e v s =
          do{ let (_, vs) = fvs ne e v s
                  e' = execEnvF ne e v s
            ; k <- kf e' v s
            ; (v', s') <- execVtables' vs
            ; lookupVtable k v' (s' `concatVtable` s)
            }
evalAssign (T.Lnode xs) = 
  do{ (u, rfvs) <- foldM (\(u, s) x -> (,) <$> pure (collectUnpackStmt u x) <*>  collectReversibleStmt s x) (Nothing, (,)) xs
    ; maybe
        (return $ \ vf fvs -> snd (rfvs vf fvs))
        (\l -> unpack l rfvs)
        u
    }
  where
    collectReversibleStmt :: ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> (EnvF -> ValueF, EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))) -> T.ReversibleStmt -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> (EnvF -> ValueF, EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')))
    collectReversibleStmt rfvs (T.ReversibleAssign keyroute l) =
      do{ get <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign l
        ; unset <- unsetPlainRoute keyroute
        ; let rfvs' vf fvs = (unset rf, assignLhs (get rf) fvs')
                where
                  (rf, fvs') = rfvs vf fvs
        ; return rfvs'
        }
    collectReversibleStmt rfvs _ = return rfvs
        
    
    collectUnpackStmt :: Maybe T.Lval -> T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt Nothing (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt x _ = x
                  
    unpack :: T.Lval -> ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> (EnvF -> ValueF,  EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))) -> Eval ((EnvF -> ValueF) -> (EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables')) -> EnvF -> EnvF -> Vtable -> Vtable -> (EnvF, Vtables'))
    unpack l rfvs = 
      do{ assignLhs <- evalAssign l
        ; let rfvs' vf fvs = assignLhs rf fvs'
                where
                  (rf, fvs') = rfvs vf fvs
        ; return rfvs'
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
  
  
