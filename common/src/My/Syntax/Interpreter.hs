{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My.Syntax.Interpreter
  ( runFile
  , browse
  , interpret
  , module My.Types
  )
where

import qualified My.Types.Syntax as P
import My.Types
import qualified My.Types.Syntax.Class as S
--import My.Eval (eval)
--import My.Eval.IO (evalIO)
--import My.Builtin (builtins)
import My.Syntax.Parser (Parser, parse, program', syntax)
--import My.Syntax.Import
import My.Syntax.Repr (Check, runCheck, buildBlock, buildBrowse, Name)
import My.Util
import System.IO (hFlush, stdout, FilePath)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.Text (Text, pack)
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Bifunctor
import Data.Semigroup ((<>))
import Data.Maybe (fromMaybe)
import Data.Void
import Data.Typeable
import Control.Applicative (liftA2)
import Control.Monad.Reader
import Control.Monad.Catch
import qualified Text.Parsec
import Bound.Scope (instantiate)

  
-- | Load a sequence of statements
readStmts :: Text -> Either MyError (Repr Assoc K (Nec Ident))
readStmts t =
    (first ParseError (parse program' "myi" t)
      >>= first DefnError . runCheck . (S.#. "output") . buildBlock . toList)
      
interpret :: Text -> Text
interpret = either (pack . displayError) (showStmts . eval) . readStmts
  where
    showStmts e = case e of
      Prim (Number d) -> pack (show d)
      Prim (Text t)   -> t
      _               -> error "component not found \"repr\""
  

-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Repr Assoc K (Nec Ident))
runFile file =
  T.readFile file <&> (\ t ->
    first ParseError (parse program' file t)
      >>= first DefnError . runCheck . (S.#. "run") . buildBlock . toList)
    >>= either
      (fail . displayError)
      (pure . eval)
  
-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
getPrompt :: Text -> IO Text
getPrompt prompt =
  flushStr prompt >> T.getLine
  
  
  
-- | Parse an expression.
readExpr :: Text -> Either MyError (Repr Assoc K Name)
readExpr t =
  first ParseError (parse (syntax <* Text.Parsec.eof) "myi" t)
  >>= first DefnError . runCheck
  
  
-- | Read-eval-print iteration
showExpr :: Repr b K a -> String
showExpr a = case a of
  Prim (Number d)  -> show d
  Prim (Text t)    -> show t
  Prim (Bool  b)   -> show b
  Prim (IOError e) -> show e
  _                -> error "eval: component not found \"repr\""

      

-- | Enter read-eval-print loop
browse
  :: IO ()
browse = first where
  first = getPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s =
    putStrLn (either
      displayError
      (showExpr . eval)
      (readExpr s))
    >> first
   
   
