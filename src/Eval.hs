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
import Data.List.NonEmpty( toList )
import qualified Data.Map as M
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = (s -> a)
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a


evalRval :: T.Rval -> Ided (ESRT DE Value)
evalRval (T.Number x) = return (return (Number x))
evalRval (T.String x) = return (return (String x))
evalRval (T.Rident x) = return (lookupEnv x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Ided (ESRT DE Value)
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
  do{ scope <- foldMap id <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return
        (do{ envs <- ask
           ; return (nn (configureEnv (scope <> initialEnv emptyTable) (toList envs)))
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
    evalUnop :: T.Unop -> Value -> DE Value
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
    evalBinop :: T.Binop -> Value -> Value -> DE Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ let
            opk = T.Key (binopSymbol sym)
            rhsk = T.Key rhsSymbol
            resk = T.Key resultSymbol
        ; op <- lookupValue opk x
        ; self <- lift (configureSelf ((\ _ -> EndoM (insertTables (return rhsk) (return y))) <> unNode op <> initialSelf emptyTables))
        ; maybe (throwUnboundVar resk) id (lookupTables resk self)
        }
evalRval (T.Import x) = evalRval x


unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return emptyNode)

overValueWithKey :: Ided (DE (T.Name Value) -> Setter' (DE Value) (DE Value))
overValueWithKey =
  do{ nn <- newNode 
    ; return (\ mk f mv -> 
        do{ v <- mv
          ; return (nn ((\ _ -> EndoM (alterTables mk f)) <> unNode v))
          })
    }

overOrNewValueWithKey :: Ided (DE (T.Name Value) -> Setter' (DE Value) (DE Value))
overOrNewValueWithKey = 
  do{ nn <- newNode
    ; return (\ mk f mv -> 
        do{ c <- unNodeOrEmpty mv
          ; return (nn ((\ _ -> EndoM (alterTables mk f)) <> c))
          })
    }
    
    
evalLaddr :: T.Laddress -> Ided (ESR (DE Value -> DE Value) -> Scope)
evalLaddr (T.Lident x) = return (scope . fmap (\ f -> (alterTable x f, return)))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Ided (ESR (DE Value -> DE Value) -> Scope)
    evalLroute (T.Route l (T.Key x)) = 
      do{ kr <- evalRval x
        ; lset <- evalLaddr l
        ; overk <- overOrNewValueWithKey
        ; return (\ fr ->
            lset
              (do{ mk <- mapESRT Identity (T.Key <$> kr)
                 ; f <- fr
                 ; return (overk mk f)
                 }))
        }
    evalLroute (T.Route l (T.Ref x)) =
      do{ lset <- evalLaddr l
        ; overk <- overOrNewValueWithKey
        ; return (\ fr ->
            lset
              (do{ f <- fr
                 ; return (overk (return (T.Ref x)) f)
                 }))
        }
    evalLroute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return (\ fr ->
            scope
              (do{ mk <- mapESRT Identity (T.Key <$> kr)
                 ; f <- fr
                 ; return (id, alterTables mk f)
                 }))
        }
    evalLroute (T.Atom (T.Ref x)) = return (\ fr ->
      scope
        (do{ f <- fr
           ; let k = T.Ref x
           ; mv <- mapESRT Identity (lookupSelf k)
           ; return (insertTable x mv, alterTables (return k) f)
           }))
    
    
unsetValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> DE Value)
unsetValueWithKey =
  do{ nn <- newNode
    ; return (\ mk mv ->
        do{ v <- mv
          ; return (nn ((\ _ -> EndoM (deleteTables mk)) <> unNode v))
          })
    }
    
    
unsetOrEmptyValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> DE Value)
unsetOrEmptyValueWithKey =
  do{ nn <- newNode
    ; return (\ mk mv -> 
        do{ c <- unNodeOrEmpty mv
          ; return (nn ((\ _ -> EndoM (deleteTables mk)) <> c))
          })
    }
    
evalStmt :: T.Stmt -> Ided Scope
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Ided Scope
    evalUnassign (T.Lident x) = return (\ _ _ -> (endo (insertTable x (throwUnboundVar x)), mempty))
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Ided Scope
    evalUnassignRoute (T.Route l (T.Key x)) =
      do{ kr <- evalRval x
        ; lset <- evalLaddr l
        ; unsetk <- unsetOrEmptyValueWithKey
        ; return
            (lset
               (do{ mk <- mapESRT Identity (T.Key <$> kr)
                  ; return (unsetk mk)
                  }))
        }
    evalUnassignRoute (T.Route l (T.Ref x)) =
      do{ lset <- evalLaddr l
        ; unsetk <- unsetOrEmptyValueWithKey
        ; return (lset (return (unsetk (return (T.Ref x)))))
        }
    evalUnassignRoute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return
            (scope
               (do{ mk <- mapESRT Identity (T.Key <$> kr)
                  ; return (id, deleteTables mk)
                  }))
        }
    evalUnassignRoute (T.Atom (T.Ref x)) =
      return
        (scope
           (do { let k = T.Ref x
               ; mv <- mapESRT Identity (lookupSelf k)
               ; return (insertTable x mv, deleteTables (return k))
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
    

viewValueWithKey :: DE (T.Name Value) -> Getter (DE Value) (DE Value)
viewValueWithKey mk mv = do{ k <- mk; v <- mv; lookupValue k v }
    
    
evalPlainRoute :: T.PlainRoute -> Ided (ESR ((Getter (DE Value) (DE Value), Setter' (DE Value) (DE Value))))
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

    
splitPlainRoute :: T.PlainRoute -> Ided (ESR (DE Value -> (DE Value, DE Value)))
splitPlainRoute (T.PlainRoute (T.Atom k)) = splitComponent k
  where
    splitComponent :: T.Name T.Rval -> Ided (ESR (DE Value -> (DE Value, DE Value)))
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

    splitValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> (DE Value, DE Value))
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
    
  
evalAssign :: T.Lval -> Ided (ESR (DE Value) -> Scope)
evalAssign (T.Laddress l) =
  do{ lset <- evalLaddr l
    ; return (lset . fmap const)
    }
evalAssign (T.Lnode xs) =
  do{ unpack <- foldMap id <$> mapM evalReversibleStmt xs
    ; maybe
        (return (execWriter . appEndoM unpack))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
  where
    evalReversibleStmt :: T.ReversibleStmt -> Ided (EndoM (Writer Scope) (ESR (DE Value)))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      -- splitPlainRoute r :: Cont Scope (Cont Classed (Eval Rval -> (Eval Rval, Eval Rval)))
      do{ splitr <- splitPlainRoute keyroute
        ; lassign <- evalAssign l
        ; return 
            (EndoM (\ vr ->
               do{ let m = splitr <*> vr
                 ; tell (lassign (snd <$> m))
                 ; return (fst <$> m)
                 }))
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> Ided (EndoM (Writer Scope) (ESR (DE Value)) -> ESR (DE Value) -> Scope)
    evalUnpack l = 
      do{ lassign <- evalAssign l
        ; return (\ unpack vr ->
            let
              (wr, scope) = runWriter (appEndoM unpack vr)
            in 
              lassign wr <> scope)
        }
        