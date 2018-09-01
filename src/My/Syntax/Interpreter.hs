{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My.Syntax.Interpreter
  ( runFile
  , browse
  , module My.Types
  , DefnError(..)
  )
where

--import My.Parser (showMy)
import My.Types.Error
import qualified My.Types.Parser as P
import My.Types
--import My.Eval (eval)
--import My.Eval.IO (evalIO)
--import My.Builtin (builtins)
import My.Syntax.Parser (Parser, parse, program', syntax)
--import My.Syntax.Import
import My.Syntax.Repr (Check, runCheck, buildBlock, DefnError(..))
import My.Util
import System.IO (hFlush, stdout, FilePath)
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Text as T
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
import Bound.Scope (instantiate, abstractEither)

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO T.Text
readPrompt prompt =
  flushStr prompt >> T.getLine


-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Repr K (Nec Ident))
runFile file =
  T.readFile file
  >>= throwLeftMy . parse program' file
  >>= throwLeftList . runCheck . buildBlock
  >>= return . eval . (`At` Key "run") . Comps . val
  
  
-- | Read-eval-print iteration
readEvalPrint :: T.Text -> IO ()
readEvalPrint =
  throwLeftMy . parse (syntax <* Text.Parsec.eof) "myi"
  >=> throwLeftList . runCheck
  >=> putStrLn . showexpr . eval
  where
    showexpr :: Repr K (P.Vis (Nec Ident) Ident) -> String
    showexpr a = case a of
      Prim (Number d)  -> show d
      Prim (Text t)    -> show t
      Prim (Bool  b)   -> show b
      Prim (IOError e) -> show e
      _                -> errorWithoutStackTrace "component missing: repr"

-- | Enter read-eval-print loop
browse :: IO ()
browse = first where
  first = readPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s = readEvalPrint s >> first
    
   
