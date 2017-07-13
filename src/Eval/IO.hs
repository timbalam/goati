{-# LANGUAGE FlexibleContexts #-}

module Eval.IO
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
import qualified Types.Error as E
import Types.Eval
import Types.Util
import Eval.Value
  
  
-- Console / Import --
flushStr :: MonadIO m => String -> m ()
flushStr str = liftIO (putStr str >> hFlush stdout)

readPrompt :: MonadIO m => String -> m String
readPrompt prompt = liftIO (flushStr prompt >> getLine)

readParser :: Parser a -> String -> Either P.ParseError a
readParser parser input = P.parse parser "myi" input
    
readProgram :: String -> Either P.ParseError T.Rval
readProgram input = T.Rnode <$> readParser program input

showProgram :: String -> String
showProgram s = either show showStmts (readProgram s)
  where
    showStmts (T.Rnode (x:xs)) = show x ++ foldr (\a b -> ";\n" ++ show a ++ b) "" xs
    
loadProgram :: String -> ReaderT (Env, Self) IX (Maybe Value)
loadProgram file =
  liftIO (readFile file) >>= either E.throwParseError return . readProgram >>= evalRvalMaybe
  
readValue :: String -> Either P.ParseError T.Rval
readValue = readParser rhs
    
evalAndPrint :: String -> ReaderT (Env, Self) IX ()
evalAndPrint s =
  do{ r <- either E.throwParseError return (readValue s)
    ; mb <- evalRvalMaybe r
    ; maybe (return ()) (liftIO . putStrLn . show) mb
    }
    
browse :: ReaderT (Env, Self) IX ()
browse = first
  where 
    first = readPrompt ">> " >>= rest
    rest ":q" = return ()
    rest s = evalAndPrint s >> first

viewEnvAt :: T.Ident -> ReaderT (Env, Self) IX (Maybe Value)
viewEnvAt k =
  do{ (env, _) <- ask
    ; maybe
        (maybe 
           (E.throwUnboundVar k)
           id
           (keyword k))
        (fmap Just . lift . viewCell)
        (M.lookup k env)
    }
  where
    keyword :: T.Ident -> Maybe (ReaderT (Env, Self) IX (Maybe Value))
    keyword (T.Ident "browse") = Just (browse >> return Nothing)
    keyword _ = Nothing
            
viewSelfAt :: T.Ident -> ReaderT (Env, Self) IX (Maybe Value)
viewSelfAt k =
 do{ (_, self) <- ask
   ; maybe (E.throwUnboundVar k) (fmap Just . lift . viewCell) (M.lookup k self)
   }
  
-- Eval --
evalRval :: T.Rval -> ReaderT (Env, Self) IX Value
evalRval r = evalRvalMaybe r >>= maybe E.throwMissing return


evalRvalMaybe :: T.Rval -> ReaderT (Env, Self) IX (Maybe Value)
evalRvalMaybe (T.Number x) = (return . Just . Number) x
evalRvalMaybe (T.String x) = (return . Just . String) x
evalRvalMaybe (T.Rident x) = viewEnvAt x
evalRvalMaybe (T.Rroute x) = evalRouteMaybe x
  where
    evalRouteMaybe :: T.Route T.Rval -> ReaderT (Env, Self) IX (Maybe Value)
    evalRouteMaybe (T.Route r x) =
      do{ v <- evalRval r
        ; vself <- lift (viewValue v)
        ; (fmap Just . lift . viewCellAt x) vself
        }
    evalRoute (T.Atom x) = viewSelfAt 
evalRvalMaybe (T.Rnode stmts) =
  do{ (env, _) <- ask
    ; scope <- fold <$> mapM evalStmt stmts
    ; v <- newNode <*> pure (configureEnv (scope <> initial env))
    ; return (Just v)
    }
evalRvalMaybe (T.App x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; u <- newNode <*> pure (unNode w <> unNode v)
    ; return (Just u)
    }
evalRvalMaybe (T.Unop sym x) =
  do{ v <- evalRval x
    ; (fmap Just . lift . evalUnop sym) v
    }
  where
    evalUnop :: T.Unop -> Value -> IX Value
    evalUnop sym (Number x) = primitiveNumberUnop sym x
    evalUnop sym (Bool x) = primitiveBoolUnop sym x
    evalUnop sym x = E.throwUnboundVar sym
evalRvalMaybe (T.Binop sym x y) =
  do{ v <- evalRval x
    ; w <- evalRval y
    ; (fmap Just . lift . evalBinop sym v) w
    }
  where
    evalBinop :: T.Binop -> Value -> Value -> IX Value
    evalBinop sym (Number x) (Number y) = primitiveNumberBinop sym x y
    evalBinop sym (Bool x) (Bool y) = primitiveBoolBinop sym x y
    evalBinop sym x y = E.throwUnboundVar sym
evalRvalMaybe (T.Import x) = 
  do{ r <- evalRval x
    ; case r of
        String s -> loadProgram s
        _ -> E.throwImportError r
    }

    
evalLaddr :: T.Laddress -> ReaderT (Env, Self) IX ((Maybe Cell -> IX (Maybe Cell)) -> Scope IXW Self IX Env)
evalLaddr (T.Lident x) = return (\ f -> EndoM (lift . lift . M.alterF f x))
evalLaddr (T.Lroute r) = evalLroute r
  where
    evalLroute :: T.Route T.Laddress -> ReaderT (Env, Self) IX ((Maybe Cell -> IX (Maybe Cell)) -> Scope IXW Self IX Env)
    evalLroute (T.Route l x) = (.) <$> evalLaddr l <*> pure (\ f -> fmap Just . cellAtMaybe x f)
    evalLroute (T.Atom x) = 
      return
        (\ f ->
           EndoM (\ env0 ->
             do{ tell (EndoM (lift . M.alterF f x) :: EndoM IXW Self)
               ; (_, self) <- ask
               ; let
                   sharedCell =
                     newCell (viewCellAt x self)
               ; M.insert x <$> sharedCell <*> pure env0
               }))
             
    
evalStmt :: T.Stmt -> ReaderT (Env, Self) IX (Scope IXW Self IX Env)
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
             ; tell (EndoM (return . M.union self) :: EndoM IXW Self)
             ; return (M.union self env0)
             }))
    }
evalStmt (T.Eval r) =
  return
    (EndoM (\ env0 -> 
       do{ es <- ask
         ; let
             eff :: () -> IX ()
             eff () = runReaderT (evalRvalMaybe r) es >> return ()
         ; tell (EndoM (\ self0 -> tell (EndoM eff) >> return self0 ))
         ; return env0
         }))

         
evalPlainRoute :: T.PlainRoute -> ReaderT (Env, Self) IX (Self -> IX Value, (Maybe Cell -> IX (Maybe Cell)) -> EndoM IX Self)
evalPlainRoute (T.PlainRoute (T.Atom x)) =
  return (viewCellAt x, EndoM . flip M.alterF x)
evalPlainRoute (T.PlainRoute (T.Route l x)) =
  do{ (lget, lset) <- evalPlainRoute l
    ; return (viewCellAt x <=< viewValue <=< lget, lset . (\ f -> fmap Just . cellAtMaybe x f))
    }
    
  
evalAssign :: T.Lval -> ReaderT (Env, Self) IX (IX Value -> Scope IXW Self IX Env)
evalAssign (T.Laddress l) =
  do{ lset <- evalLaddr l
    ; return (\ m -> lset (\ _ -> Just <$> newCell m))
    }
evalAssign (T.Lnode xs) =
  do{ (unpack, c) <- (fmap fold . mapM evalReversibleStmt) xs
    ; maybe 
        (return (\ m -> unpack (m >>= viewValue) ))
        (\ l -> do{ lunpack <- evalUnpack l; return (lunpack unpack c) })
        (getAlt (foldMap (Alt . collectUnpackStmt) xs))
    }
  where
    evalReversibleStmt :: T.ReversibleStmt -> ReaderT (Env, Self) IX (IX Self -> Scope IXW Self IX Env, EndoM IX Self)
    evalReversibleStmt (T.ReversibleAssign keyroute l) =
      do{ lassign <- evalAssign l
        ; (lget, lset) <- evalPlainRoute keyroute
        ; return (\ mself -> lassign (mself >>= lget), lset (\ _ -> return Nothing))
        }
    evalReversibleStmt _ = return mempty
    
    
    collectUnpackStmt :: T.ReversibleStmt -> Maybe T.Lval
    collectUnpackStmt (T.ReversibleUnpack lhs) = Just lhs
    collectUnpackStmt _ = Nothing
    
    
    evalUnpack :: T.Lval -> ReaderT (Env, Self) IX ((IX Self -> Scope IXW Self IX Env) -> EndoM IX Self -> IX Value -> Scope IXW Self IX Env)
    evalUnpack l = 
      do{ lassign <- evalAssign l
        ; return (\ unpack c m ->
            let
              p = unpack (m >>= viewValue)
              m' = newNode <*> (m >>= \ v -> return (mapEndoM (lift . lift) c <> unNode v))
            in 
              lassign m' <> p)
        }
        