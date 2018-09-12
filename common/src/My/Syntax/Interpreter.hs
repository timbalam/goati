{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My.Syntax.Interpreter
  ( runFile
  , browse
  , runStmts
  , module My.Types
  , DefnError(..)
  )
where

--import My.Parser (showMy)
import My.Types.Error
import qualified My.Types.Parser as P
import My.Types
import qualified My.Types.Syntax.Class as S
--import My.Eval (eval)
--import My.Eval.IO (evalIO)
--import My.Builtin (builtins)
import My.Syntax.Parser (Parser, parse, program', syntax)
--import My.Syntax.Import
import My.Syntax.Repr (Check, runCheck, buildBlock, buildBrowse, Name, DefnError(..))
import My.Util
import System.IO (hFlush, stdout, FilePath)
import Data.List.NonEmpty (NonEmpty(..), toList)
import Data.Text (Text)
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
runStmts :: Text -> IO (Repr Assoc K (Nec Ident))
runStmts t =
  throwLeftMy (parse program' "myi" t)
  >>= throwLeftList . runCheck . (S.#. "output") . buildBlock
  >>= pure . eval
  

-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Repr Assoc K (Nec Ident))
runFile file =
  T.readFile file
  >>= throwLeftMy . parse program' file
  >>= throwLeftList . runCheck . (S.#. "run") . buildBlock
  >>= pure . eval
  
  
-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: Text -> IO Text
readPrompt prompt =
  flushStr prompt >> T.getLine
  
  
  
-- | Parse an expression.
parseExpr :: Text -> IO (Repr Assoc K Name)
parseExpr t =
  throwLeftMy (parse (syntax <* Text.Parsec.eof) "myi" t)
  >>= throwLeftList . runCheck
  
  
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
  first = readPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s = parseExpr s >>= putStrLn . showExpr . eval >> first
   
   
