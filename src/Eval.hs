{-# LANGUAGE FlexibleContexts #-}

module Eval
  ( evalRval
  , browse
  , loadProgram
  , readProgram
  , readValue
  , primitiveBindings
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
import Data.IORef
import System.IO
  ( putStr
  , hFlush
  , stdout
  )
  
import Text.Parsec.String ( Parser )
import qualified Text.Parsec as P
import Parser
  ( program
  , rhs
  )
import qualified Types.Parser as T
import qualified Error as E
import Types.Eval

type Getter s a = (s -> a)
type Setter s t a b = (a -> b) -> s -> t
type Setter' s a = Setter s s a a

-- Console / Import --

flushStr :: MonadIO m => String -> m ()
flushStr str = liftIO (putStr str >> hFlush stdout)

readPrompt :: MonadIO m => String -> m String
readPrompt prompt = liftIO (flushStr prompt >> getLine)

readParser :: Parser a -> String -> Either E.Error a
readParser parser input = either (throwError . E.Parser "parse error") return (P.parse parser "myc" input)
 
readValue :: String -> Either E.Error T.Rval
readValue input = readParser rhs input
    
evalAndPrint :: String -> ESRT IX ()
evalAndPrint s =
  catchError
    (do{ r <- (lift . lift . ExceptT . return . readValue) s
       ; v <- evalRval r
       ; (liftIO . putStrLn . show) v
       })
    (liftIO . putStrLn . show)
    
browse :: ESRT IX ()
browse = first
  where 
    first = readPrompt ">> " >>= rest
    rest ":q" = return ()
    rest s = evalAndPrint s >> first
    
readProgram :: String -> Either E.Error T.Rval
readProgram input = T.Rnode <$> readParser program input

showProgram :: String -> String
showProgram s = either show showStmts (readProgram s)
  where
    showStmts (T.Rnode (x:xs)) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
    
loadProgram :: String -> ESRT IX Value
loadProgram file =
  lift (lift (ExceptT (readFile file >>= return . readProgram))) >>= evalRval

viewEnvAt :: T.Ident -> ESRT IX Value
viewEnvAt k =
  do{ (env, _) <- ask
    ; maybe
        (maybe 
           (throwUnboundVar k)
           id
           (keyword k))
        (lift . viewCell)
        (M.lookup k env)
    }
  where
    keyword :: T.Ident -> Maybe (ESRT IX Value)
    keyword (T.Ident "browse") = Just (browse >> newSymbol)
    keyword _ = Nothing
            
viewSelfAt :: T.Ident -> ESRT IX Value
viewSelfAt k =
 do{ (_, self) <- ask
   ; maybe (throwUnboundVar k) (lift . viewCell) (M.lookup k self)
   }
  
-- Eval --
evalRval :: T.Rval -> ESRT IX Value
evalRval (T.Number x) = return (Number x)
evalRval (T.String x) = return (String x)
evalRval (T.Rident x) = viewEnvAt x
evalRval (T.Rroute x) = evalRoute x
  where
    evalRoute :: T.Route T.Rval -> ESRT IX Value
    evalRoute (T.Route r x) =
      do{ v <- evalRval r
        ; vself <- lift (viewValue v)
        ; lift (viewCellAt x vself)
        }
    evalRoute (T.Atom x) = viewSelfAt x
evalRval (T.Rnode []) = newSymbol
evalRval (T.Rnode stmts) =
  do{ (env, _) <- ask
    ; scope <- fold <$> mapM evalStmt stmts
    ; newNode <*> pure (configureScope (scope <> initial env))
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
    evalUnop sym x = throwUnboundVar (show sym)
evalRval (T.Binop sym x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; lift (evalBinop sym v w)
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IX Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = throwUnboundVar (show sym)
evalRval (T.Import x) = 
  do{ r <- evalRval x
    ; case r of
        String s -> loadProgram s
        _ -> throwError (E.ImportError "Import error" (show r))
    }

    
evalLaddr :: T.Laddress -> ESRT IX ((Maybe Cell -> IX (Maybe Cell)) -> Scope)
evalLaddr (T.Lident x) = return (\ f -> EndoM (lift . lift . M.alterF f x))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> ESRT IX ((Maybe Cell -> IX (Maybe Cell)) -> Scope)
    evalLroute (T.Route l x) = (.) <$> evalLaddr l <*> pure (\ f -> fmap Just . cellAtMaybe x f)
    evalLroute (T.Atom x) = 
      return
        (\ f ->
           EndoM (\ env0 ->
             do{ tell (EndoM (lift . M.alterF f x))
               ; (_, self) <- ask
               ; let
                   sharedCell =
                     newCell (viewCellAt x self)
               ; M.insert x <$> sharedCell <*> pure env0
               }))
             
    
evalStmt :: T.Stmt -> ESRT IX Scope
evalStmt (T.Declare l) =
  do{ lset <- evalLaddr l
    ; return (lset (\ _ -> return Nothing))
    }
evalStmt (T.Assign l r) =
  do{ lassign <- evalAssign l
    ; return (EndoM (\ env0 ->
        do{ es <- ask
          ; appEndoM ((lassign . runReaderT (evalRval r)) es) env0
          }))
    }
evalStmt (T.Unpack r) = 
  do{ v <- evalRval r
    ; return
        (EndoM (\ env0 ->
           do{ self <- lift (lift (viewValue v))
             ; tell (EndoM (return . M.union self))
             ; return (M.union self env0)
             }))
    }
evalStmt (T.Eval r) =
  return
    (EndoM (\ env0 -> 
       do{ es <- ask
         ; let eff () = runReaderT (evalRval r) es >> return ()
         ; tell (EndoM (\ self0 -> tell (EndoM eff) >> return self0 ))
         ; return env0
         }))

         
evalPlainRoute :: T.PlainRoute -> ESRT IX (Self -> IX Value, (Maybe Cell -> IX (Maybe Cell)) -> EndoM IX Self)
evalPlainRoute (T.PlainRoute (T.Atom x)) =
  return (viewCellAt x, EndoM . flip M.alterF x)
evalPlainRoute (T.PlainRoute (T.Route l x)) =
  do{ (lget, lset) <- evalPlainRoute l
    ; return (viewCellAt x <=< viewValue <=< lget, lset . (\ f -> fmap Just . cellAtMaybe x f))
    }
    
  
evalAssign :: T.Lval -> ESRT IX (IX Value -> Scope)
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
    evalReversibleStmt :: T.ReversibleStmt -> ESRT IX (IX Self -> Scope, EndoM IX Self)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ lassign <- evalAssign l
        ; (lget, lset) <- evalPlainRoute keyroute
        ; return (\ mself -> lassign (mself >>= lget), lset (\ _ -> return Nothing))
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> ESRT IX ((IX Self -> Scope) -> EndoM IX Self -> IX Value -> Scope)
    evalUnpack l = 
      do{ lassign <- evalAssign l
        ; return (\ unpack c m ->
            let
              p = unpack (m >>= viewValue)
              m' = newNode <*> (m >>= \ v -> return (EndoM (lift . lift . appEndoM c) <> unNode v))
            in 
              lassign m' <> p)
        }
        