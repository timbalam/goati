{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My.Syntax.Interpreter
  ( runFile
  , browse
  , interpret
  , module My.Types.Eval
  , module My.Types.Error
  )
where

import qualified My.Types.Syntax as P
import My.Types.Error
import My.Types.Eval
import qualified My.Types.Syntax.Class as S
--import My.Eval.IO (evalIO)
--import My.Builtin (builtins)
import My.Syntax.Parser (Parser, parse, program', syntax)
--import My.Syntax.Import
import My.Util
import System.IO (hFlush, stdout, FilePath)
import Data.Bifunctor
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Semigroup ((<>))
import Data.Text (Text, pack)
import qualified Data.Text.IO as T
import Data.Typeable
import Data.Void
import Control.Applicative (liftA2)
import Control.Monad.Reader
import Control.Monad.Catch
import qualified Text.Parsec
import Bound.Scope (instantiate)

  
-- | Load a sequence of statements
readStmts :: Text -> Self (Dyn' Ident)
readStmts t = either
  (Block . throwDyn . StaticError . ParseError)
  (snd . eval . inspector)
  (parse program' "myi" t)
  where
    inspector stmts = 
      S.block_ 
        [ S.self_ "inspect" S.#=
          "Define \".inspect\" and see the value here!"
        ] S.# S.block_ stmts S.#. "inspect"
      
interpret :: Text -> Text
interpret = pack . displayValue displayDyn' . readStmts
  

-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Self (Dyn' Ident))
runFile file = do
  t <- T.readFile file
  either
    (fail . displayErrorList displayStaticError)
    return
    (either
      (Left . pure . ParseError)
      (checkEval . (S.#. "run") . S.block_)
      (parse program' file t))
  
  
-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
getPrompt :: Text -> IO Text
getPrompt prompt =
  flushStr prompt >> T.getLine
  
  
  
-- | Parse an expression.
readExpr
  :: Text
  -> Either [StaticError Ident] (Self (Dyn' Ident))
readExpr t = either
  (Left . pure . ParseError)
  checkEval
  (parse (syntax <* Text.Parsec.eof) "myi" t)


-- | Enter read-eval-print loop
browse
  :: IO ()
browse = first where
  first = getPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s =
    putStrLn (either
      (displayErrorList displayStaticError)
      (displayValue displayDyn')
      (readExpr s))
    >> first
   
   
