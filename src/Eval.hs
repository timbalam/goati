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

evalRval :: T.Rval -> ESRT X Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = asks fst >>= viewAt x
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> ESRT X Value
    evalRoute (T.Route r (T.Key x)) =
      do{ k <- evalRval x
        ; v <- evalRval r
        ; vself <- lift (viewSelf v)
        ; lift (viewAt (T.Key k) vself)
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ v <- evalRval r
        ; vself <- lift viewSelf v
        ; lift (viewAt (T.Ref x) vself)
        }
    evalRoute (T.Atom (T.Key x)) =
      do{ k <- evalRval x
        ; self <- asks snd
        ; lift (viewAt (T.Key k) self)
        }
    evalRoute (T.Atom (T.Ref x)) = asks snd >>= viewAt (T.Ref x)
evalRval (T.Rnode []) = newSymbol
evalRval (T.Rnode stmts) =
  do{ env <- asks fst
    ; b <- fold evalStmt stmts
    ; newNode <*> pure (configureEnv (buildScope b <> initial env))
    }
evalRval (T.App x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; newNode <*> pure (unNode w <> unNode v)
    }
evalRval (T.Unop sym x) =
  do{ v <- evalRval x
    ; lift (evalUnop sym v)
    }
  where
    evalUnop :: T.Unop -> Value -> X Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = viewSelf x >>= viewAt (T.Key (unopSymbol sym))
evalRval (T.Binop sym x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; lift (evalBinop sym v w)
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
        ; xself <- viewSelf x
        ; op <- viewAt opk xself
        ; opself <- configure (EndoM (return . M.insert rhsk y) <> unNode op)
        ; viewAt resk opself
        }
evalRval (T.Import x) = evalRval x
    
evalLaddr :: T.Laddress -> ESRT X ((Maybe Value -> X Maybe Value) -> ScopeB)
evalLaddr (T.Lident x) = return (\ f _ -> (EndoM (M.alterF f x), mempty))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> ESRT X ((Maybe Value -> X (Maybe Value)) -> (EndoM X Env, EndoM X SelfB))
    evalLroute (T.Route l (T.Key x)) = 
      do{ k <- T.Key <$> evalRval x
        ; evalLaddr l <*> pure (valueAt k)
        }
    evalLroute (T.Route l (T.Ref x)) = evalLaddr l <*> pure (valueAt (T.Ref x))
    evalLroute (T.Atom (T.Key x)) =
      do{ k <- T.Key <$> evalRval x
        ; return (\ f _ -> (mempty, EndoM (M.alterF f k)))
        }
    evalLroute (T.Atom (T.Ref x)) =
      do{ let k = T.Ref x
        ; return (\ f (_, self) -> (Endo (M.alter (\ _ -> M.lookup k self) x), Endo (M.alterF f k)) })
        }))
             
    
evalStmt :: T.Stmt -> ESRT X ScopeB
evalStmt (T.Declare l) = evalLaddr l <*> pure (\ _ -> return Nothing)
evalStmt (T.Assign l r) =
  do{ lassign <- lassignr
    ; return (\ es -> lassign (runReaderT (evalRval r) es) es)
    }
evalStmt (T.Unpack r) =
  return
    (\ es -> 
       let
         mself = viewSelf (runReaderT (evalRval r) es)
       in
         (mempty, EndoM (\ self0 -> M.union <$> mself <*> pure self0)))
evalStmt (T.Eval r) =
  return
    (\ es ->
       let
         effects = viewSelf (runReaderT (evalRval r) es)
       in
         (mempty, EndoM (\ self0 -> effects >> return self0)))

    
evalPlainRoute :: T.PlainRoute -> ESRT X (Self -> X Value, (Maybe Value -> X (Maybe Value)) -> Maybe Value -> X (Maybe Value))
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ k <- T.Key <$> evalRval x
    ; return (viewAt k, valueAt k)
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ let k = T.Ref x
    ; return (viewAt k, valueAt k)
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ k <- T.Key <$> evalRval x
    ; (lget, lset) <- llensr
    ; return (lget <=< viewSelf <=< viewAt k, lset . valueAt k)
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ (lget, lset) <- llensr
    ; let k = T.Ref x
    ; return (lget <=< viewSelf <=< viewAt k, lset . valueAt k)
    }
    
  
evalAssign :: T.Lval -> ESRT X (X Value -> ScopeB)
evalAssign (T.Laddress l) = evalLaddr l <*> pure (\ m _ -> Just <$> m)
evalAssign (T.Lnode xs) =
  do{ unpack <- fold <$> mapM evalReversibleStmt xs
    ; maybe
        (return (\ m es -> execWriter (appEndoM (unpack es (m >>= viewSelf)) m)))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
  where
    evalReversibleStmt :: T.ReversibleStmt -> ESRT X ((Env, Self) -> X Self -> EndoM (Writer (EndoM X Env, EndoM Self)) (X Value))
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ llensr <- evalPlainRoute keyroute
        ; lassignr <- evalAssign l
        ; return 
            (do{ lassign <- lassignr
               ; (lget, lset) <- llensr
               ; return
                   (\ es mself ->
                      EndoM (\ m0 ->
                        do{ tell (lassign (mself >>= lget) es)
                          ; return (m0 >>= lset (\ _ -> return Nothing) . Just)
                          }))
               })
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> ESRT X (((Env, Self) -> X Self -> EndoM (Writer (EndoM X Env, EndoM X Self)) (X Value)) -> X Value -> ScopeB)
    evalUnpack l = 
      do{ lassign <- lassignr
        ; return (\ unpack m es ->
            let
              mself = m >>= viewSelf
              (m', p) = runWriter (appEndoM (unpack es mself) m)
            in
              lassign m' es <> p)
        }
        