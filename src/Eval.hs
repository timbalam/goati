{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  )
where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class( liftIO )
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Cont
import Control.Monad.Identity
import Control.Monad.Trans.Class( lift )
import Control.Applicative
  ( (<|>)
  , liftA2
  )
import Control.Monad( ap )
import Data.Monoid
  ( Alt(Alt)
  , getAlt
  )
import qualified Data.Map as M
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = (a -> Const a b) -> s -> Const s t
type Setter s t a b = (a -> Identity b) -> s -> Identity t
type Setter' s a = Setter s s a a

getter :: (s -> a) -> Getter s a
getter get = const (Const . get)

setter :: ((a -> b) -> s -> t) -> Setter s t a b
setter set f = Identity . set (runIdentity . f)

view :: Getter s a -> s -> a
view l s = getConst (l Const s)

over :: Setter s t a b -> (a -> b) -> s -> t
over l f s = runIdentity (l (Identity . f) s)

lens :: Functor f => Getter s a -> Setter s t a b -> (a -> f b) -> s -> f t
lens get set f s = over set . const <$> f (view get s)
    
    

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
evalRval (T.Rnode []) = return (return newSymbol)
evalRval (T.Rnode stmts) =
  do{ scope <- foldMap id <$> mapM evalStmt stmts
    ; nn <- newNode
    ; return
        (do{ env <- askEnv
           ; return (nn (configureEnv (scope <> initial env)))
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
      do{ op <- lookupValue (T.Key (binopSymbol sym)) x
        ; xop <- getEndoM (unNode op) emptyTables
        ; xop' <- insertTables (return (T.Key rhsSymbol)) (return y) xop
        ; let k = T.Key resultSymbol
        ; maybe (throwUnboundVar k) id (lookupTables (return k) xop')
        }
evalRval (T.Import x) = evalRval x


unNodeOrEmpty :: MonadError E.Error m => m Value -> m Node
unNodeOrEmpty mv = catchUnboundVar (unNode <$> mv) (return emptyNode)

setValueWithKey :: Ided (DE (T.Name Value) -> Setter' (DE Value) (DE Value))
setValueWithKey =
  do{ nn <- newNode 
    ; return (\ mk ->
        setter (\ f mv -> 
          do{ v <- mv
            ; return (nn (Endo(return . alterTables (mk >>= throwUnboundVar) mk f) <> unNode v))
            }))
    }

setOrNewValueWithKey :: Ided (DE (T.Name Value) -> Setter' (DE Value) (DE Value))
setOrNewValueWithKey = 
  do{ nn <- newNode
    ; return (\ mk ->
        setter (\ f mv -> 
          do{ c <- unNodeOrEmpty mv
            ; return (nn (Endo (return . alterTables (mk >>= throwUnboundVar) mk f) <> c))
            }))
    }
    
    
evalLaddr :: T.Laddress -> Ided (ESR (DE Value -> DE Value) -> Scope)
evalLaddr (T.Lident x) = return (scope . fmap (\ f -> (alterTable (throwUnboundVar x) x f, return)))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Ided (ESR (DE Value -> DE Value) -> Scope)
    evalLroute (T.Route l (T.Key x)) = 
      do{ kr <- evalRval x
        ; lset <- evalLaddr l
        ; setk <- setOrNewValueWithKey
        ; return (\ fr ->
            lset
              (do{ mk <- T.Key <$> mapESRT Identity kr
                 ; f <- fr
                 ; return (over (setk mk) f)
                 }))
        }
    evalLroute (T.Route l (T.Ref x)) =
      do{ lset <- evalLaddr l
        ; setk <- setOrNewValueWithKey
        ; return (\ fr ->
            lset
              (do{ f <- fr
                 ; return (over (setk (return (T.Ref x))) f)
                 }))
        }
    evalLroute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return (\ fr ->
            scope
              (do{ mk <- T.Key <$> mapESRT Identity kr
                 ; f <- fr
                 ; return (id, alterTables (mk >>= throwUnboundVar) (T.Key <$> mk) f)
                 }))
        }
    evalLroute (T.Atom (T.Ref x)) = return (\ fr ->
      scope
        (do{ f <- fr
           ; let k = T.Ref x
           ; mv <- mapESRT Identity (lookupSelf k)
           ; return (insertTable k mv, alterTables (throwUnboundVar k) (return k) f)
           }))
    
    
unsetValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> DE Value)
unsetValueWithKey =
  do{ nn <- newNode
    ; return (\ mk mv ->
        do{ k <- T.Key <$> mk
          ; v <- mv
          ; return (nn (Endo (insertTables (return k) (throwUnboundVar k)) <> unNode v))
          })
    }
    
    
unsetOrEmptyValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> DE Value)
unsetOrEmptyValueWithKey =
  do{ nn <- newNode
    ; return (\ mk mv -> 
        do{ k <- T.Key <$> mk
          ; c <- unNodeOrEmpty mv
          ; return (nn (Endo (return . deletesTable k) <> c))
          })
    }
    
evalStmt :: T.Stmt -> Ided Scope
evalStmt (T.Declare l) = evalUnassign l
  where
    evalUnassign :: T.Laddress -> Ided Scope
    evalUnassign (T.Lident x) = return (Endo (return . fmap (insertTable x (throwUnboundVar x))))
    evalUnassign (T.Lroute r) = evalUnassignRoute r
    
    
    evalUnassignRoute :: T.Route T.Laddress -> Ided Scope
    evalUnassignRoute (T.Route l (T.Key x)) =
      do{ kr <- evalRval x
        ; lset <- evalLaddr l
        ; return (lset
            (do{ mk <- T.Key <$> mapESRT Identity kr
               ; return (unsetOrEmptyValueWithKey mk)
               })
        }
    evalUnassignRoute (T.Route l (T.Ref x)) =
      do{ lset <- evalLaddr l
        ; return (lset (return (unsetOrEmptyValueWithKey (T.Ref x))))
        }
    evalUnassignRoute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return (scope
            (do{ mk <- T.Key <$> mapESRT Identity kr
               ; return (return, insertTables mk (throwUnboundVar =<< mk))
               })
        }
    evalUnassignRoute (T.Atom (T.Ref x)) =
      return (scope
        (do { let k = T.Ref x
            ; mv <- lookupSelf k
            ; return (insertTable x mv, insertTables (return k) (throwUnboundVar k))
            }))
evalStmt (T.Assign l r) =
  do{ vr <- evalRval
    ; lassign <- evalAssign l
    ; return (lassign (mapESRT Identity vr))
    }
evalStmt (T.Unpack r) =
  do{ vr <- evalRval r
    ; return
        (scope
           (do{ v <- mapESRT Identity vr
              ; self <- lift (configureSelf (unNode v <> initial emptyTables))
              ; return (id, unionTables self)
              }))
    }
evalStmt (T.Eval r) =
  do{ vr <- evalRval r
    ; return
        (scope
           (do{ v <- mapESRT Identity vr
              ; _ <- lift (configureSelf (unNode v <> initial emptyTables))
              ; return (id, return)
              }))
    }
    

getValueWithKey :: DE (T.Name Value) -> Getter (DE Value) (DE Value)
getValueWithKey mk = getter(\ mv -> do{ k <- mk; v <- mv; lookupValue k v })
    
    
evalPlainRoute :: Functor f => T.PlainRoute -> Ided (ESR ((DE Value -> f (DE Value)) -> DE Value -> f (DE Value)))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ kr <- evalRval x
    ; setk <- setValueWithKey
    ; return
        (do{ mk <- T.Key <$> mapESRT Identity kr
           ; return (lens (getValueWithKey mk) (setk mk))
           })
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ setk <- setValueWithKey
    ; let mk = return (T.Ref x)
    ; return (return (lens (getValueWithKey mk) (setk mk)))
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ kr <- evalRval x
    ; llensr <- evalPlainRoute l
    ; setk <- setValueWithKey
    ; return 
        (do{ mk <- T.Key <$> mapESRT Identity kr
           ; llens <- lensr
           ; return (llens . lens (getValueWithKey mk) (setk mk))
           })
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; setk <- setValueWithKey
    ; return
        (do{ llens <- llensr
           ; let mk = return (T.Ref x)
           ; return (llens . lens (getValueWithKey mk) (setk mk))
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
            (do{ mk <- T.Key <$> mapESRT Identity kr
               ; return (splitk mk)
               })
        }
    splitComponent (T.Ref x) =
      splitValueWithKey <*> pure (T.Ref x)

    splitValueWithKey :: Ided (DE (T.Name Value) -> DE Value -> (DE Value, DE Value))
    splitValueWithKey =
      do{ unsetk <- unsetValueWithKey
        ; return (\ mk mv -> (view (getValueWithKey mk) mv, unsetk mk mv))
        }
splitPlainRoute (T.PlainRoute (T.Route l (T.Key r))) =
  do{ kr <- evalRval r
    ; llensr <- evalPlainRoute l
    ; unsetk <- unsetValueWithKey
    ; return
        (do{ mk <- T.Key <$> mapESRT Identity kr
           ; llens <- llensr
           ; return (\ mv -> (view (llens . getValueWithKey mk) mv, over llens (unset mk) mv)))
           })
    }
splitPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; unsetk <- unsetValueWithKey
    ; return
        (do{ llens <- llensr
           ; let mk = return (T.Ref x)
           ; return (\ mv -> (view (llens . getValueWithKey mk) mv, over llens (unsetk mk) mv))
           })
    }
    
  
evalAssign :: T.Lval -> Ided (ESR (DE Value) -> Scope)
evalAssign (T.Laddress (T.Lident x)) vr =
  return (scope (do{ mv <- vr; return (insertTable x mv, return)))
evalAssign (T.Laddress (T.Lroute l)) vr =
  do{ lset <- evalLaddr l
    ; return (lset (const <$> vr))
    }
evalAssign (T.Lnode xs) vr =
  do{ unpacks <- foldMap id <$> mapM evalReversibleStmt xs
    ; maybe
        (return (execWriter (getEndoM unpack vr)))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack vr) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
    
    evalReversibleStmt :: T.ReversibleStmt -> Ided (EndoM (Writer Scope) (ESR (DE Value)))
    evalReversibleStmt (T.ReversibleAssign keyroute l) = 
      -- splitPlainRoute r :: Cont Scope (Cont Classed (Eval Rval -> (Eval Rval, Eval Rval)))
      do{ splitr <- splitPlainRoute keyroute
        ; lassign <- evalAssign l
        ; return 
            (Endo (\ vr ->
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
        ; return (\ unpacks vr ->
            let
              (scope, wr) = runWriter (getEndoM unpacks vr)
            in 
              lassign wr <> scope)
        }
        