{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  )
where
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Writer hiding ( Endo(Endo), appEndo )
import Control.Monad.Cont
import Control.Monad.Identity
import Control.Monad.Trans.Class
import Control.Applicative
import Data.Monoid ( Alt(Alt), getAlt )
import Data.Semigroup ( Max(Max) )
import Data.Foldable ( fold )
import Data.Maybe ( mapMaybe )
import qualified Data.Map as M
import qualified Data.Set as S
 
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = (s -> a)
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a

evalRval :: T.Rval -> ESRT IX Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = viewEnvAt x
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> ESRT IX Value
    evalRoute (T.Route r (T.Key x)) =
      do{ k <- evalRval x
        ; v <- evalRval r
        ; vself <- lift (viewValue v)
        ; lift (viewCellAt (T.Key k) vself)
        }
    evalRoute (T.Route r (T.Ref x)) =
      do{ v <- evalRval r
        ; vself <- lift (viewValue v)
        ; lift (viewCellAt (T.Ref x) vself)
        }
    evalRoute (T.Atom (T.Key x)) =
      do{ k <- evalRval x
        ; viewSelfAt (T.Key k)
        }
    evalRoute (T.Atom (T.Ref x)) = viewSelfAt (T.Ref x)
evalRval (T.Rnode []) = newSymbol
evalRval (T.Rnode stmts) =
  do{ (env, _) <- ask
    ; b <- fold <$> mapM evalStmt stmts
    ; newNode <*> pure (configureScope (buildScope b <> initial env))
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
    evalUnop :: T.Unop -> Value -> IX Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = viewValue x >>= viewCellAt (T.Key (unopSymbol sym))
evalRval (T.Binop sym x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; lift (evalBinop sym v w)
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IX Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y =
      do{ let
            opk = T.Key (binopSymbol sym)
            rhsk = T.Key rhsSymbol
            resk = T.Key resultSymbol
        ; xself <- viewValue x
        ; op <- viewCellAt opk xself
        ; opself <- configureClassed (EndoM (\ x -> M.insert rhsk <$> newCell (return y) <*> pure x) <> unNode op)
        ; viewCellAt resk opself
        }
evalRval (T.Import x) = evalRval x
    
evalLaddr :: T.Laddress -> ESRT IX ((Maybe Cell -> IX (Maybe Cell)) -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env)
evalLaddr (T.Lident x) = return (\ f _ -> EndoM (lift . M.alterF f x))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> ESRT IX ((Maybe Cell -> IX (Maybe Cell)) -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env)
    evalLroute (T.Route l (T.Key x)) = 
      do{ k <- T.Key <$> evalRval x
        ; (.) <$> evalLaddr l <*> pure (\ f -> fmap Just . cellAtMaybe k f)
        }
    evalLroute (T.Route l (T.Ref x)) = (.) <$> evalLaddr l <*> pure (\ f -> fmap Just . cellAtMaybe (T.Ref x) f)
    evalLroute (T.Atom (T.Key x)) =
      do{ k <- T.Key <$> evalRval x
        ; return (\ f _ -> EndoM (\ env0 -> do{ tell (EndoM (M.alterF f k)); return env0 }))
        }
    evalLroute (T.Atom (T.Ref x)) = 
      do{ let k = T.Ref x :: T.Name Value
        ; return
            (\ f (_, self) ->
               EndoM (\ env0 ->
                 do{ tell (EndoM (M.alterF f k))
                   ; let
                       sharedCell =
                         newCell (viewCellAt k self)
                   ; M.insert x <$> sharedCell <*> pure env0
                   }))
        }
             
    
evalStmt :: T.Stmt -> ESRT IX ScopeB
evalStmt (T.Declare l) =
  do{ lset <- evalLaddr l
    ; return (lset (\ _ -> return Nothing))
    }
evalStmt (T.Assign l r) =
  do{ lassign <- evalAssign l
    ; return (\ es -> lassign (runReaderT (evalRval r) es) es)
    }
evalStmt (T.Unpack r) = 
  do{ v <- evalRval r
    ; return (\ es ->
        EndoM (\ env0 ->
          do{ self <- lift (viewValue v)
            ; tell (EndoM (return . M.union self))
            ; let 
                sharedMap = M.fromAscList (mapMaybe shareCellIdentKey (M.toAscList self))
            ; return (M.union sharedMap env0)
            }))
    }
  where
    shareCellIdentKey :: (T.Name a, Cell) -> Maybe (T.Ident, Cell)
    shareCellIdentKey (T.Ref x, ref) = Just (x, ref)
    shareCellIdentKey (T.Key _, _) = Nothing
evalStmt (T.Eval r) =
  return
    (\ es ->
       let
         effects = runReaderT (evalRval r) es >>= viewValue
       in
         EndoM ((lift effects >>) . return))

         
evalPlainRoute :: T.PlainRoute -> ESRT IX (Self -> IX Value, (Maybe Cell -> IX (Maybe Cell)) -> EndoM IX Self)
evalPlainRoute (T.PlainRoute (T.Atom (T.Key x))) =
  do{ k <- T.Key <$> evalRval x
    ; return (viewCellAt k, EndoM . flip M.alterF k)
    }
evalPlainRoute (T.PlainRoute (T.Atom (T.Ref x))) =
  do{ let k = T.Ref x
    ; return (viewCellAt k, EndoM . flip M.alterF k)
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Key x))) =
  do{ k <- T.Key <$> evalRval x
    ; (lget, lset) <- evalPlainRoute l
    ; return (viewCellAt k <=< viewValue <=< lget, lset . (\ f -> fmap Just . cellAtMaybe k f))
    }
evalPlainRoute (T.PlainRoute (T.Route l (T.Ref x))) =
  do{ (lget, lset) <- evalPlainRoute l
    ; let k = T.Ref x
    ; return (viewCellAt k <=< viewValue <=< lget, lset . (\ f -> fmap Just . cellAtMaybe k f))
    }
    
  
evalAssign :: T.Lval -> ESRT IX (IX Value -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env)
evalAssign (T.Laddress l) =
  do{ lset <- evalLaddr l
    ; return (\ m -> lset (\ _ -> Just <$> newCell m))
    }
evalAssign (T.Lnode xs) =
  do{ (unpack, c) <- fold <$> mapM (evalReversibleStmt) xs
    ; maybe 
        (return (\ m -> unpack (m >>= viewValue) ))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack c) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
    
  where
    evalReversibleStmt :: T.ReversibleStmt -> ESRT IX (IX Self -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env, EndoM IX Self)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ lassign <- evalAssign l
        ; (lget, lset) <- evalPlainRoute keyroute
        ; return (\ mself -> lassign (mself >>= lget), lset (\ _ -> return Nothing))
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> ESRT IX ((IX Self -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env) -> EndoM IX Self -> IX Value -> (Env, Self) -> EndoM (WriterT (EndoM IX Self) IX) Env)
    evalUnpack l = 
      do{ lassign <- evalAssign l
        ; return (\ unpack c m ->
            let
              p = unpack (m >>= viewValue)
              m' = newNode <*> (m >>= \ v -> return (EndoM (lift . appEndoM c) <> unNode v))
            in 
              lassign m' <> p)
        }
        