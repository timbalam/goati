{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE ImpredicativeTypes #-}
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
import Utils.Lens
  ( Lens'
  , Setter'
  , lens
  , sets
  , view
  , over
  , set
  )

lensValueF :: KeyF -> Eval (Lens' ValueF ValueF)
lensValueF kf = 
  do{ nn <- newNode
    ; let set vf wf v =
            do{ val <- vf v
              ; let kf' _ = kf v
                    wf' _ = wf v
              ; return $ nn (inserts kf' wf' `concats` unNode val)
              }
    ; return lens (lookupValueF kf) set
    }
  
 
evalName :: T.Name T.Rval -> EnvF -> Eval KeyF
evalName (T.Key r) e = evalRval r e >>= \f -> fmap T.Key . f
evalName (T.Ref x) e = return (\_ -> return $ T.Ref x)

evalRval :: T.Rval -> Eval (EnvF -> ValueF)
evalRval (T.Number x) = return (\_ _ -> return $ Number x)
evalRval (T.String x) = return (\_ _ -> return $ String x)
evalRval (T.Rident x) = return (lookupEnvF (T.Ref x))
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Eval (EnvF -> ValueF)
    evalRoute (T.Route r x) =
      do{ vf <- evalRval r
        ; kf <- evalName x
        ; return (\e -> lookupValueF (vf e) (kf e))
        }
    evalRoute (T.Atom x) =
      do{ kf <- evalName x
        ; return (lookupSelf . kf)
      where
        lookupSelf kf v =
          do{ k <- kf v
            ; k `lookupVtable` v
            }
evalRval (T.Rnode stmts) =
  do{ (e, vs) <- foldM (collectStmt) (emptyEnvF, \_ -> emptyVtables)) stmts
    ; nn <- newNode
    ; let vf pe v =
            do{ let pe' _ = pe v
                    e' = e `concatEnvF` pe
              ; return $ nn (vs e)
              }
    ; return vf
    }
  where
    collectStmt :: EnvR -> (EnvF, EnvF -> Vtables) -> T.Stmt -> Eval (EnvF, EnvF -> Vtables)
    collectStmt ie (e, vs) (T.Assign l r) =
      do{ vf <- evalRval r
        ; (ee, gg) <- evalAssign l <$> vf
        ; let vs' e = gg e `concats` vs e
        ; return (ee `concatEnvF` e, vs')
        }
    collectStmt ie (f, vs) (T.Unpack r) =
      do{ vf <- evalRval r ie
        ; let gg l r =
                do{ lr <- concatVtable <$> l <*> r
                  ; val <- vf lr
                  ; execVtables (unNode val)
                  }
        ; return (f, gg `concats` vs)
        }
    collectStmt ie (f, vs) (T.Eval r) =
      do{ vf <- evalRval r ie
        ; let gg l r =
                do{ lr <- concatVtable <$> l <*> r
                  ; _ <- vf lr
                  ; return emptyVtable
                  }
        ; return (f, gg `concats` vs)
        }
evalRval (T.App x y) ie =
  do{ xf <- evalRval x ie
    ; yf <- evalRval y ie
    ; nn <- newNode
    ; let vf v =
            do{ xval <- xf v
              ; yval <- yf v
              ; return $ nn (unNode xval `concats` unNode yval)
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
      do{ v <- execVtables (unNode x)
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
      do{ xv <- execVtables (unNode x)
        ; xop <- T.Key (binopSymbol s) `lookupVtable` xv
        ; let kf _ = return $ T.Key rhsSymbol
              vf _ = return $ y
              vs = inserts kf vf `concats` unNode xop
        ; v <- execVtables vs
        ; T.Key resultSymbol `lookupVtable` v
        }
        
        
evalAssign :: T.Lval -> EnvR -> Eval (ValueF -> (EnvF, Vtables))
evalAssign (T.Laddress x) ie = evalAssignLaddress x ie
  where
    evalAssignLaddress :: T.Laddress -> EnvR -> Eval (ValueF -> (EnvF, Vtables))
    evalAssignLaddress (T.Lident x) _ = return assign
      where
        assign vf = let f' _ = Vtable [(T.Ref x, vf)] in (f', emptyVtables)
    evalAssignLaddress (T.Lroute x) ie = evalAssignRoute x ie
    
    
    evalAssignRoute :: T.Route T.Laddress -> EnvR -> Eval (ValueF -> (EnvF, Vtables))
    evalAssignRoute (T.Route l x) ie =
      do{ kf <- evalName x ie
        ; lvf <- lookupLaddress l ie
        ; nn <- newNode
        ; let set vf wf v =
                do{ ws <- catchError (unNode <$> vf v) handleUnboundVar
                  ; let kf' _ = kf v
                        vf' _ = wf v
                  ; return $ nn (inserts kf' vf' `concats` ws)
                  }
        ; assignLaddress <- evalAssignLaddress l ie
        ; return (assignLaddress . set lvf)
        }
    evalAssignRoute (T.Atom x) ie =
      do{ kf <- evalName x ie
        ; let assignKey vf = (f, vs)
                where
                  vs = inserts kf vf
                  f v =
                    do{ k <- kf v
                      ; let vf' _ = k `lookupVtable` v
                      ; return $ Vtable [(k, vf')]
                      }
        ; return assignKey
        }
        
        
    lookupLaddress :: T.Laddress -> EnvR -> Eval ValueF
    lookupLaddress (T.Lident x) ie = return lookupIdent
      where
        lookupIdent v =
          do{ f <- liftIO (readIORef ie)
            ; lookupEnvF (T.Ref x) f v
            }
    lookupLaddress (T.Lroute r) ie = lookupRoute r ie
       
       
    lookupRoute :: T.Route T.Laddress -> EnvR -> Eval ValueF
    lookupRoute (T.Route l key) ie = lookupValueF <$> evalName key ie <*> lookupLaddress l ie
    lookupRoute (T.Atom key) ie = lookupSelf <$> evalName key ie
      where
        lookupSelf kf v =
          do{ k <- kf v
            ; k `lookupVtable` v
            }
      
      
    handleUnboundVar :: E.Error -> IOExcept Vtables
    handleUnboundVar (E.UnboundVar _ _) = return emptyVtables
    handleUnboundVar err = throwError err
evalAssign (T.Lnode xs) ie = 
  do{ let inits vf = (vf, emptyEnvF, emptyVtables)
    ; (u, rfvs) <- foldM (\(u, s) x -> (,) <$> return (collectUnpackStmt u x) <*>  collectReversibleStmt ie s x) (Nothing, inits) xs
    ; let sndAndThrd (_, a, b) = (a, b)
    ; maybe
        (return $ sndAndThrd . rfvs)
        (\l -> unpack l ie rfvs)
        u
    }
  where
    collectReversibleStmt :: EnvR -> (ValueF -> (ValueF, EnvF, Vtables)) -> T.ReversibleStmt -> Eval (ValueF -> (ValueF, EnvF, Vtables))
    collectReversibleStmt ie rfvs (T.ReversibleAssign keyroute lhs) =
      do{ get <- viewPlainRoute keyroute ie
        ; assignLhs <- evalAssign lhs ie
        ; unset <- unsetPlainRoute keyroute ie
        ; let rfvs' vf = (r', ff `concatEnvF` f, gg `concats` vs)
                where
                  (r, f, vs) = rfvs vf
                  r' = unset r
                  vf' = get r
                  (ff, gg) = assignLhs vf'
        ; return rfvs'
        }
    collectReversibleStmt _ rfvs _ = return rfvs
        
    
    collectUnpackStmt :: Maybe T.Lval -> T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt Nothing (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt x _ = x
                  
    unpack :: T.Lval -> EnvR -> (ValueF -> (ValueF, EnvF, Vtables)) -> Eval (ValueF -> (EnvF, Vtables))
    unpack l ie rfvs =
      do{ assignLhs <- evalAssign l ie
        ; nn <- newNode
        ; let fvs' vf = (ff `concatEnvF` f, gg `concats` vs)
                where
                  (r, f, vs) = rfvs vf
                  (ff, gg) = assignLhs r
        ; return fvs'
        }
        
    
    viewPlainRoute :: T.PlainRoute -> EnvR -> Eval (ValueF -> ValueF)
    viewPlainRoute (T.PlainRoute (T.Atom key)) ie =
      do{ kf <- evalName key ie
        ; return $ lookupValueF kf
        }
    viewPlainRoute (T.PlainRoute (T.Route l key)) ie =
      do{ kf <- evalName key ie
        ; (.) <$> (pure $ lookupValueF kf) <*> viewPlainRoute l ie
        }
        
        
    lensPlainRoute :: T.PlainRoute -> EnvR -> Eval (Lens' ValueF ValueF)
    lensPlainRoute (T.PlainRoute (T.Atom key)) ie =
      do{ kf <- evalName key ie 
        ; lensValueF kf
        }
    lensPlainRoute (T.PlainRoute (T.Route l key)) ie =
      do{ kf <- evalName key ie
        ; (.) <$> lensValueF kf <*> lensPlainRoute l ie
        }
    
    
    unsetPlainRoute :: T.PlainRoute -> EnvR -> Eval (ValueF -> ValueF)
    unsetPlainRoute (T.PlainRoute (T.Atom key)) ie = unsetKey key ie
    unsetPlainRoute (T.PlainRoute (T.Route l key)) ie = over <$> lensPlainRoute l ie <*> unsetKey key ie
        
    
    unsetKey :: T.Name T.Rval -> EnvR -> Eval (ValueF -> ValueF)
    unsetKey key ie =
      do{ kf <- evalName key ie
        ; nn <- newNode
        ; let deleteKey vf v =
                do{ val <- vf v
                  ; let kf' _ = kf v
                  ; return $ nn (kf `deletes` unNode val)
                  }
        ; return deleteKey
        }
  
  
