{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  )
where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding (Endo(Endo), appEndo)
import Control.Monad.Cont
import Control.Monad.Identity
import Control.Monad.Trans.Class
import Control.Applicative
import Data.Monoid( Alt(Alt), getAlt )
import Data.Semigroup ( Max(Max) )
import Data.List.NonEmpty( cons )
import qualified Data.Map as M
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = (s -> a)
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a


evalRval :: T.Rval -> Ided (ESRT DX Value)
evalRval (T.Number x) = return (return (Number x))
evalRval (T.String x) = return (return (String x))
evalRval (T.Rident x) = return (lookupEnv x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Ided (ESRT DX Value)
    evalRoute (T.Route r (T.Key x)) =
      do{ kr <- evalRval x
        ; vr <- evalRval r
        ; return 
            (do { k <- kr
                ; v <- vr
                ; liftToESRT (lookupValue (T.Key k) v)
                })
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ vr <- evalRval r
        ; return
            (do { v <- vr
                --; let key = T.Ref x :: T.Name Value
                ; liftToESRT (lookupValue (T.Ref x) v)
                })
        }
    evalRoute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return
            (do{ k <- kr
               ; lookupSelf (T.Key k)
               })
        }
    evalRoute (T.Atom (T.Ref x)) = return (lookupSelf (T.Ref x))
evalRval (T.Rnode []) = do{ v <- newSymbol; return (return v) }
evalRval (T.Rnode stmts) =
  do{ scopeBuilder <- foldMap id <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return
        (do{ envs <- ask
           ; return (nn (configureEnv (buildScope scopeBuilder <> initial (cons emptyTable envs))))
           })
    }
evalRval (T.App x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; nn <- newNode
    ; return 
        (do{ v <- vr
           ; w <- wr
           ; return (nn (unNode w <> unNode v))
           })
    }
evalRval (T.Unop sym x) =
  do{ vr <- evalRval x
    ; return
        (do { v <- vr
            ; liftToESRT (evalUnop sym v)
            })
    }
  where
    evalUnop :: T.Unop -> Value -> DX Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = lookupValue (T.Key (unopSymbol sym)) x
evalRval (T.Binop sym x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return 
        (do{ v <- vr
           ; w <- wr
           ; liftToESRT (evalBinop sym v w)
           })
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> DX Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ let
            opk = T.Key (binopSymbol sym)
            rhsk = T.Key rhsSymbol
            resk = T.Key resultSymbol
        ; op <- lookupValue opk x
        ; selfs <- lift (configureSelf (EndoM (_ -> do{ t <- insertTables (return rhsk) (return y) emptyTables; return (t :| []) }) <> unNode op))
        ; let mb = getAlt (foldMap (Alt . lookupTables resk) selfs) 
        ; maybe (throwUnboundVar resk) id mb
        }
evalRval (T.Import x) = evalRval x
    
    
evalLaddr :: T.Laddress -> Ided (ESR (DX (ValB -> X ValB) -> (Endo EnvB, EndoM XIO SelfB)))
evalLaddr (T.Lident x) =return (return (\ mf -> (EndoM (alterSelf x mf), mempty)))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Ided (ESR ((DX (ValB -> X ValB) -> (Endo EnvB, EndoM XIO SelfB)))
    evalLroute (T.Route l (T.Key x)) = 
      do{ kr <- evalRval x
        ; lsetr <- evalLaddr l
        ; alter <- alterValB
        ; return 
            (do{ mk <- mapESRT Identity (T.Key <$> kr)
               ; lset <*> pure (\ mf -> alter <$> mk <*> mf)
               })
        }
    evalLroute (T.Route l (T.Ref x)) =
      do{ lset <- evalLaddr l
        ; alter <- alterValB
        ; return (lset <*> pure (\mf -> alter (T.Ref x) <$> mf))
        }
    evalLroute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return
            (return
               (do{ mk <- mapESRT Identity (T.Key <$> kr)
                  ; return (\ mf -> (mempty, Endo (deferTables (alterSelfB <$> mk <*> pure mf))))
                  }))
        }
    evalLroute (T.Atom (T.Ref x)) =
      return
        (return
           (do{ let k = T.Ref x
              ; mv <- mapESRT Identity (lookupSelf k)
              ; return (\ mf -> (Endo (insertEnvB x mv), Endo (return . alterSelfB k mf)))
              }))
              
    
unsetValueWithKey :: Ided (DX (T.Name Value) -> DX Value -> DX Value)
unsetValueWithKey =
  do{ nn <- newNode
    ; return (\ mk mv ->
        do{ v <- mv
          ; return (nn ((EndoM (return . deleteTables mk)) <> unNode v))
          })
    }
    
evalStmt :: T.Stmt -> Ided Scope
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Ided Scope
    evalUnassign (T.Lident x) = return (\ _ _ -> (EndoM (return . deleteEnvB x), mempty))
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Ided Scope
    evalUnassignRoute (T.Route l (T.Key x)) =
      do{ kr <- evalRval x
        ; lsetr <- evalLaddr l
        ; delete <- deleteValB
        ; return
            (scope
               (do{ mk <- mapESRT Identity (T.Key <$> kr)
                  ; lsetr <*> pure (do{ k <- mk; return (delete k) })
                  }))
        }
    evalUnassignRoute (T.Route l (T.Ref x)) =
      do{ lsetr <- evalLaddr l
        ; delete <- deleteValB
        ; return (scope (lsetr <*> pure (return (delete (T.Ref x)))))
        }
    evalUnassignRoute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return
            (scope
               (do{ mk <- mapESRT Identity (T.Key <$> kr)
                  ; return (mempty, EndoM (deferTables (do{ k <- mk; return (return . deleteSelfB k) })))
                  }))
        }
    evalUnassignRoute (T.Atom (T.Ref x)) =
      return
        (scope
           (do { let k = T.Ref x
               ; mv <- mapESRT Identity (lookupSelf k)
               ; return (Endo (insertEnv x mv), Endo (return . deleteSelfB k))
               }))
evalStmt (T.Assign l r) =
  do{ vr <- evalRval r
    ; lassign <- evalAssign l
    ; return (lassign (mapESRT Identity vr))
    }
evalStmt (T.Unpack r) =
  do{ vr <- evalRval r
    ; return
        (scope
           (do{ mself <- mapESRT Identity (do{ v <- vr; liftToESRT (lift (configureSelf (unNode v <> initialSelf emptyTables))) })
              ; return (id, unionTables mself)
              }))
    }
evalStmt (T.Eval r) =
  do{ vr <- evalRval r
    ; return
        (scope
           (do{ mv <- mapESRT Identity (do{ v <- vr; liftToESRT (lift (configureSelf (unNode v <> initialSelf emptyTables))) })
              ; return (id, \ super -> undefer mv >> return super)
              }))
    }
    
overValueWithKey :: Ided (DX (T.Name Value) -> Setter' (DX Value) (DX Value))
overValueWithKey =
  do{ nn <- newNode 
    ; return (\ mk f mv -> 
        do{ v <- mv
          ; return (nn ((EndoM (\ selfs -> alterTables mk f selfs)) <> unNode v))
          })
    }
    

viewValueWithKey :: DX (T.Name Value) -> Getter (DX Value) (DX Value)
viewValueWithKey mk mv = do{ k <- mk; v <- mv; lookupValue k v }
    
    
evalPlainRoute :: T.PlainRoute -> Ided (ESR ((DX Value -> (Endo EnvB, EndoM XIO SelfB)) -> SelfD))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ kr <- evalRval x
    ; alter <- alterValB
    ; return
        (do{ k <- T.Key <$> kr
           ; return (insertSelfB)
           })
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ alter <- alterValB
    ; let k = T.Ref x
    ; return (return (lookupVal k, alter k))
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ kr <- evalRval x
    ; llensr <- evalPlainRoute l
    ; alter <- alterValB
    ; return
        (do{ k <- kr
           ; (lget, lset) <- llensr
           ; return (lget <=< lookupValue k, lset . alter k)
           })
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; alter <- alterValB
    ; let k = T.Ref x
    ; return
        (do{ (lget, lset) <- llensr
           ; return (lget <=< lookupValue k, lset . alter k)
           })
    }
    
evalPlainRoute :: T.PlainRoute -> Ided (ESR ((Getter (DX Value) (DX Value), Setter' (DX Value) (DX Value))))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ kr <- evalRval x
    ; overk <- overValueWithKey
    ; return
        (do{ mk <- mapESRT Identity (T.Key <$> kr)
           ; return (viewValueWithKey mk, overk mk)
           })
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ overk <- overValueWithKey
    ; let mk = return (T.Ref x)
    ; return (return (viewValueWithKey mk, overk mk))
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ kr <- evalRval x
    ; llensr <- evalPlainRoute l
    ; overk <- overValueWithKey
    ; return 
        (do{ mk <- mapESRT Identity (T.Key <$> kr)
           ; (lget, lset) <- llensr
           ; return (lget . viewValueWithKey mk, lset . overk mk)
           })
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; overk <- overValueWithKey
    ; return
        (do{ (lget, lset) <- llensr
           ; let mk = return (T.Ref x)
           ; return (lget . viewValueWithKey mk, lset . overk mk)
           })
    }

    
splitPlainRoute :: T.PlainRoute -> Ided (ESRT DX (Value -> (DX Value, EndoM X ValB))))
splitPlainRoute (T.PlainRoute (T.Atom k)) = splitComponent k
  where
    splitComponent :: T.Name T.Rval -> Ided (ESRT DX (Value -> (DX Value, EndoM X ValB)))
    splitComponent (T.Key r) = 
      do{ kr <- evalRval r
        ; splitk <- splitValueWithKey
        ; return
            (do{ mk <- mapESRT Identity (T.Key <$> kr)
               ; return (splitk mk)
               })
        }
    splitComponent (T.Ref x) =
      do{ splitk <- splitValueWithKey
        ; return (return (splitk (return (T.Ref x))))
        }

    splitValueWithKey :: Ided (DX (T.Name Value) -> DX Value -> (DX Value, DX Value))
    splitValueWithKey =
      do{ unsetk <- unsetValueWithKey
        ; return (\ mk mv -> (viewValueWithKey mk mv, unsetk mk mv))
        }
splitPlainRoute (T.PlainRoute (T.Route l (T.Key r))) =
  do{ kr <- evalRval r
    ; llensr <- evalPlainRoute l
    ; unsetk <- unsetValueWithKey
    ; return
        (do{ mk <- mapESRT Identity (T.Key <$> kr)
           ; (lget, lset) <- llensr
           ; return (\ mv -> (lget (viewValueWithKey mk mv), lset (unsetk mk) mv))
           })
    }
splitPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; unsetk <- unsetValueWithKey
    ; return
        (do{ (lget, lset) <- llensr
           ; let mk = return (T.Ref x)
           ; return (\ mv -> (lget (viewValueWithKey mk mv), lset (unsetk mk) mv))
           })
    }
    
  
evalAssign :: T.Lval -> Ided (ESR (DX Value) -> Scope)
evalAssign (T.Laddress l) =
  do{ lset <- evalLaddr l
    ; insert <- insertValB
    ; return (lset . fmap insert)
    }
evalAssign (T.Lnode xs) =
  do{ unpack <- foldMap id <$> mapM evalReversibleStmt xs
    ; maybe
        (return (execWriter . appEndoM unpack))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
  where
    evalReversibleStmt :: T.ReversibleStmt -> Ided (ESR (DX Value) -> EndoM (Writer Scope) ValB)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ llensr <- evalPlainRoute keyroute
        ; lassign <- evalAssign l
        ; return 
            (\ vr ->
               let m = 
                 mapESRT Identity
                   (do{ v <- vr
                      ; (lget, lset) <- llensr
                      ; return (lget v, 
            
               do{ let m = do{ v <- vr
                 ; tell (lassign (snd <$> m))
                 ; return (fst <$> m)
                 }))
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> Ided (EndoM (Writer Scope) (ESR (DX Value)) -> ESR (DX Value) -> Scope)
    evalUnpack l = 
      do{ lassign <- evalAssign l
        ; return (\ unpack vr ->
            let
              (wr, scope) = runWriter (appEndoM unpack vr)
            in 
              lassign wr <> scope)
        }
        