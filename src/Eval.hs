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


evalRval :: T.Rval -> Ided (ESRT X Value)
evalRval (T.Number x) = return (return (Number x))
evalRval (T.String x) = return (return (String x))
evalRval (T.Rident x) = return (lookupEnv x)
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> Ided (ESRT X Value)
    evalRoute (T.Route r (T.Key x)) =
      do{ kr <- evalRval x
        ; vr <- evalRval r
        ; return 
            (do { k <- kr
                ; v <- vr
                ; lift (lookupValue (T.Key k) v)
                })
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ vr <- evalRval r
        ; return
            (do { v <- vr
                ; lift (lookupValue (T.Ref x) v)
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
  do{ br <- fmap (fmap fold) (mapM evalStmt stmts)
    ; nn <- newNode
    ; return
        (do{ env <- asks fst
           ; b <- br
           ; return (nn (configureEnv (buildScope b <> initial env)))
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
            ; lift (evalUnop sym v)
            })
    }
  where
    evalUnop :: T.Unop -> Value -> X Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = lookupValue (T.Key (unopSymbol sym)) x
evalRval (T.Binop sym x y) =
  do{ vr <- evalRval x
    ; wr <- evalRval y
    ; return 
        (do{ v <- vr
           ; w <- wr
           ; lift (evalBinop sym v w)
           })
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> X Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ let
            opk = T.Key (binopSymbol sym)
            rhsk = T.Key rhsSymbol
            resk = T.Key resultSymbol
        ; op <- lookupValue opk x
        ; self <- configureSelf (EndoM (M.insert rhsk y) <> unNode op)
        ; viewAt resk self
        }
evalRval (T.Import x) = evalRval x
    
valueAt ::  Ided (T.Name Value -> (Maybe Value -> X (Maybe Value)) -> Maybe Value -> X (Maybe Value))
valueAt =
  do{ nn <- newNode
    ; return (\ k f mb -> return (Just (nn (Endo (M.alterF f k) <> maybe mempty unNode mb))))
    }
    
evalLaddr :: T.Laddress -> Ided (ESRT X ((Maybe Value -> X Maybe Value) -> Scope))
evalLaddr (T.Lident x) = return (return (\ f _ -> (EndoM (M.alterF f x), mempty)))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> Ided (ESRT X ((Maybe Value -> X (Maybe Value)) -> (EndoM X Env, EndoM X SelfB)))
    evalLroute (T.Route l (T.Key x)) = 
      do{ kr <- evalRval x
        ; lsetr <- evalLaddr l
        ; at <- valueAt
        ; return (lsetr <*> (at . T.Key <$> kr))
        }
    evalLroute (T.Route l (T.Ref x)) =
      do{ lsetr <- evalLaddr l
        ; at <- valueAt
        ; return (lsetr <*> pure (at (T.Ref x)))
        }
    evalLroute (T.Atom (T.Key x)) =
      do{ kr <- evalRval x
        ; return
            (return
               (do{ k <- T.Key <$> kr
                  ; return (\ f _ -> (mempty, EndoM (M.alterF f k)))
                  }))
        }
    evalLroute (T.Atom (T.Ref x)) =
      return
        (return
           (do{ let k = T.Ref x
              ; return (\ f (_, self) -> (Endo (M.alter (\ _ -> M.lookup k self) x), Endo (M.alterF f k)) })
              }))
             
    
evalStmt :: T.Stmt -> Ided (ESRT X Scope)
evalStmt (T.Declare l) = 
  do{ lsetr <- evalLaddr l
    ; return (lsetr <*> pure (\ _ -> return Nothing))
    }
evalStmt (T.Assign l r) =
  do{ lassignr <- evalAssign l 
    ; vr <- evalRval r
    ; return
        (do{ lassign <- lassignr
           ; return (\ es -> lassign (runReaderT vr es) es)
           })
    }
evalStmt (T.Unpack r) =
  do{ vr <- evalRval r
    ; return
        (return
           (\ es -> 
              let
                mself' = configureSelf (unNode (runReaderT vr es))
              in
                (mempty, EndoM (\ self -> M.union <$> mself' <*> pure self))))
    }
evalStmt (T.Eval r) =
  do{ vr <- evalRval r
    ; return
        (return
           (\ es ->
              let
                effects = configureSelf (unNode (runReaderT vr es))
              in 
                (mempty, EndoM (\ self -> effects >> return self))))
    }

    
evalPlainRoute :: T.PlainRoute -> Ided (ESRT X (Value -> X Value, (Maybe Value -> X (Maybe Value)) -> Maybe Value -> X (Maybe Value)))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ kr <- evalRval x
    ; at <- valueAt
    ; return
        (do{ k <- T.Key <$> kr
           ; return (lookupValue k, at k)
           })
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ let k = T.Ref x
    ; at <- valueAt
    ; return (return (lookupValue k, at k))
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ kr <- evalRval x
    ; llensr <- evalPlainRoute l
    ; at <- valueAt
    ; return 
        (do{ k <- T.Key <$> kr
           ; (lget, lset) <- llensr
           ; return (lget <=< lookupValue k, lset . at k)
           })
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ llensr <- evalPlainRoute l
    ; at <- valueAt
    ; return
        (do{ (lget, lset) <- llensr
           ; let k = T.Ref x
           ; return (lget <=< lookupValue k, lset . at k)
           })
    }
    
  
evalAssign :: T.Lval -> Ided (ESRT X (X Value -> Scope))
evalAssign (T.Laddress l) =
  do{ lsetr <- evalLaddr l
    ; return (lsetr <*> pure (const . fmap Just))
    }
evalAssign (T.Lnode xs) =
  do{ unpack <- fold <$> mapM evalReversibleStmt xs
    ; maybe
        (return (execWriter . appEndoM unpack))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
  where
    evalReversibleStmt :: T.ReversibleStmt -> Ided (ESRT X ((Env, Self) -> EndoM (Writer (EndoM X Env, EndoM Self)) (X Value)))
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ llensr <- evalPlainRoute keyroute
        ; lassignr <- evalAssign l
        ; return 
            (do{ lassign <- lassignr
               ; (lget, lset) <- llensr
               ; return
                   (\ es ->
                      EndoM (\ m ->
                        do{ tell (lassign (m >>= lget) es)
                          ; return (m >>= lset (\ _ -> return Nothing) . Just)
                          }))
               })
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> Ided (ESRT X (((Env, Self) -> EndoM (Writer (EndoM X Env, EndoM X Self)) (X Value)) -> X Value -> Scope))
    evalUnpack l = 
      do{ lassignr <- evalAssign l
        ; nn <- newNode
        ; return
            (do{ lassign <- lassignr
               ; return (\ unpack m es ->
                   let
                     (m', scope) = runWriter (appEndoM (unpack es) m)
                   in
                     lassign m' <> scope)
               })
        }
        