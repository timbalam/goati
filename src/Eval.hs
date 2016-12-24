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
  , EnvR
  , ValueF
  , KeyF
  , lookupValueF
  , Vtables
  , execVtables
  , emptyVtables
  , inserts
  , concats
  , deletes
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
type Sets' s a = (a -> a) -> (s -> s)
  
viewValueF :: (EnvF -> KeyF) -> Gets' (EnvF -> ValueF) (EnvF -> ValueF)
viewValueF kf vf e = lookupValueF (kf e) (vf e)


overValueF :: (EnvF -> KeyF) -> Eval (Sets' (EnvF -> ValueF) (EnvF -> ValueF))
overValueF kf =
  do{ nn <- newNode
    ; let over f vf e v =
            do{ val <- vf e v
              ; let kf' _ = kf e v
                    wf' _ = f (viewValueF kf vf) e v 
              ; return $ nn (inserts kf' wf' `concats` unNode val)
              }
    ; return over
    }


viewSelf :: (EnvF -> KeyF) -> EnvF -> ValueF    
viewSelf kf e v =
  do{ k <- kf e v
    --; liftIO . putStrLn $ showVtable v
    ; k `lookupVtable` v
    }

    
showVtable :: Vtable -> String
showVtable (Vtable xs) = show (map fst xs)
    
 
evalName :: T.Name T.Rval -> Eval (EnvF -> KeyF)
evalName (T.Key r) = (\f e v -> T.Key <$> f e v) <$> evalRval r
evalName (T.Ref x) = return (\ _ _ -> return $ T.Ref x)

evalRval :: T.Rval -> Eval (EnvF -> ValueF)
evalRval (T.Number x) = return (\_ _ -> return $ Number x)
evalRval (T.String x) = return (\_ _ -> return $ String x)
evalRval (T.Rident x) = return (lookupEnvF (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (EnvF -> ValueF)
    evalRoute (T.Route r x) = viewValueF <$> evalName x <*> evalRval r
    evalRoute (T.Atom x) = viewSelf <$> evalName x
evalRval (T.Rnode stmts) =
  do{ let inits _ = (emptyEnvF, emptyVtables)
    ; fvs <- foldM collectStmt inits stmts
    ; nn <- newNode
    ; let vf e v = return $ nn vs
            where
              e' _ = e v
              (ne, vs) = fvs (ne `concatEnvF` e')
    ; return vf
    }
  where
    collectStmt :: (EnvF -> (EnvF, Vtables)) -> T.Stmt -> Eval (EnvF -> (EnvF, Vtables))
    collectStmt fvs (T.Assign l r) =
      do{ fvs' <- evalAssign l <*> evalRval r
        ; let fvs'' e = (ff `concatEnvF` f, gg `concats` vs)
                where
                  (f, vs) = fvs e
                  (ff, gg) = fvs' e
        ; return fvs''
        }
    collectStmt fvs (T.Unpack r) =
      do{ vf <- evalRval r
        ; let fvs' e = (f, gg `concats` vs)
                where
                  gg l r =
                    do{ lr <- concatVtable <$> l <*> r
                      ; val <- vf e lr
                      ; execVtables (unNode val)
                      }
                  (f, vs) = fvs e
        ; return fvs'
        }
    collectStmt fvs (T.Eval r) =
      do{ vf <- evalRval r
        ; let fvs' e = (f, gg `concats` vs)
                where
                  gg l r =
                    do{ lr <- concatVtable <$> l <*> r
                      ; _ <- vf e lr
                      ; return emptyVtable
                      }
                  (f, vs) = fvs e
        ; return fvs'
        }
evalRval (T.App x y) =
  do{ xf <- evalRval x
    ; yf <- evalRval y
    ; nn <- newNode
    ; let vf e v =
            do{ xval <- xf e v
              ; yval <- yf e v
              ; return $ nn (unNode yval `concats` unNode xval)
              }
    ; return vf
    }
evalRval (T.Unop s x) =
  do{ xf <- evalRval x
    ; let vf e v =
            do{ val <- xf e v
              ; evalUnop s val
              }
    ; return vf
    }
  where
    evalUnop :: T.Unop -> Value -> IOExcept Value
    evalUnop s (Number x) = primitiveNumberUnop s x
    evalUnop s (Bool x) = primitiveBoolUnop s x
    evalUnop s x =
      do{ v <- execVtables (unNode x)
        ; T.Key (unopSymbol s) `lookupVtable` v
        }
evalRval (T.Binop s x y) =
  do{ xf <- evalRval x
    ; yf <- evalRval y
    ; let vf e v =
            do{ xval <- xf e v
              ; yval <- yf e v
              ; evalBinop s xval yval
              }
    ; return vf
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IOExcept Value
    evalBinop s (Number x) (Number y) = primitiveNumberBinop s x y
    evalBinop s (Bool x) (Bool y) = primitiveBoolBinop s x y
    evalBinop s x y = 
      do{ xv <- execVtables (unNode x)
        ; xop <- T.Key (binopSymbol s) `lookupVtable` xv
        ; let kf _ = return $ T.Key rhsSymbol
              vf _ = return $ y
              vs = inserts kf vf `concats` unNode xop
        ; v <- execVtables vs
        ; T.Key resultSymbol `lookupVtable` v
        }
        
        
evalAssign :: T.Lval -> Eval ((EnvF -> ValueF) -> EnvF -> (EnvF, Vtables))
evalAssign (T.Laddress x) = evalAssignLaddress x
  where
    evalAssignLaddress :: T.Laddress -> Eval ((EnvF -> ValueF) -> EnvF -> (EnvF, Vtables))
    evalAssignLaddress (T.Lident x) = return assign
      where
        assign vf e = let f' _ = Vtable [(T.Ref x, vf e)] in (return . f', emptyVtables)
    evalAssignLaddress (T.Lroute x) = evalAssignRoute x
    
    
    evalAssignRoute :: T.Route T.Laddress -> Eval ((EnvF -> ValueF) -> EnvF -> (EnvF, Vtables))
    evalAssignRoute (T.Route l x) =
      do{ nn <- newNode
        ; let assignKey kf vf wf e v =
                do{ kf e v >>= liftIO . putStrLn . show
                  ; liftIO . putStrLn $ showVtable v
                  ; ws <- catchUnboundVar emptyVtables (unNode <$> vf e v)
                  ; execVtables ws >>= liftIO . putStrLn . showVtable
                  ; let kf' _ = kf e v
                        vf' _ = wf e v
                  ; return $ nn (inserts kf' vf' `concats` ws)
                  }
        ; (.) <$> evalAssignLaddress l <*> (assignKey <$> evalName x <*> lookupLaddress l)
        }
    evalAssignRoute (T.Atom k) = assignSelf <$> evalName k
      where
        assignSelf kf vf e = (return . setEnv k, inserts (kf e) (vf e))
        setEnv (T.Key _) _ = emptyVtable
        setEnv (T.Ref x) v = let vf' _ = T.Ref x `lookupVtable` v in Vtable [(T.Ref x, vf')]
        
        
    lookupLaddress :: T.Laddress -> Eval (EnvF -> ValueF)
    lookupLaddress (T.Lident x) = return $ lookupEnvF (T.Ref x)
    lookupLaddress (T.Lroute r) = lookupRoute r
       
       
    lookupRoute :: T.Route T.Laddress -> Eval (EnvF -> ValueF)
    lookupRoute (T.Route l key) = viewValueF <$> evalName key <*> lookupLaddress l
    lookupRoute (T.Atom key) = viewSelf <$> evalName key
evalAssign (T.Lnode xs) = 
  do{ let inits vf e = (vf e, emptyEnvF, emptyVtables)
    ; (u, rfvs) <- foldM (\(u, s) x -> (,) <$> pure (collectUnpackStmt u x) <*>  collectReversibleStmt s x) (Nothing, inits) xs
    ; let sndAndThrd (_, a, b) = (a, b)
    ; maybe
        (return $ \vf -> sndAndThrd . rfvs vf)
        (\l -> unpack l rfvs)
        u
    }
  where
    collectReversibleStmt :: ((EnvF -> ValueF) -> EnvF -> (ValueF, EnvF, Vtables)) -> T.ReversibleStmt -> Eval ((EnvF -> ValueF) -> EnvF -> (ValueF, EnvF, Vtables))
    collectReversibleStmt rfvs (T.ReversibleAssign keyroute lhs) =
      do{ get <- viewPlainRoute keyroute
        ; assignLhs <- evalAssign lhs
        ; unset <- unsetPlainRoute keyroute
        ; let rfvs' vf e = (r', ff `concatEnvF` f, gg `concats` vs)
                where
                  (r, f, vs) = rfvs vf e
                  cr _ = r
                  r' = unset cr e
                  vf' = get cr
                  (ff, gg) = assignLhs vf' e
        ; return rfvs'
        }
    collectReversibleStmt rfvs _ = return rfvs
        
    
    collectUnpackStmt :: Maybe T.Lval -> T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt Nothing (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt x _ = x
                  
    unpack :: T.Lval -> ((EnvF -> ValueF) -> EnvF -> (ValueF, EnvF, Vtables)) -> Eval ((EnvF -> ValueF) -> EnvF -> (EnvF, Vtables))
    unpack l rfvs =
      do{ assignLhs <- evalAssign l
        ; nn <- newNode
        ; let fvs' vf e = (ff `concatEnvF` f, gg `concats` vs)
                where
                  (r, f, vs) = rfvs vf e
                  (ff, gg) = assignLhs (\_ -> r) e
        ; return fvs'
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
      do{ kf <- evalName key
        ; nn <- newNode
        ; let deleteKey vf e v =
                do{ val <- vf e v
                  ; let kf' _ = kf e v
                  ; return $ nn (deletes kf' (unNode val))
                  }
        ; return deleteKey
        }
  
  
