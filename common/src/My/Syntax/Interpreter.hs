{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My.Syntax.Interpreter
  ( runFile
  , browse
  , parseDefns
  , parseExpr
  , evalAndShow
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
import My.Syntax.Repr (Check, runCheck, buildAbsParts, buildBrowse, Name, DefnError(..))
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

  
-- Console / Import --
flushStr :: Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: Text -> IO Text
readPrompt prompt =
  flushStr prompt >> T.getLine
  
  
-- | Load file as an expression.
parseDefns :: Text -> IO (Browse Name K (Repr (Browse Name) K Name))
parseDefns =
  throwLeftMy . parse program' "myi"
  >=> throwLeftList . runCheck . buildBrowse
  >=> return . fmap (fmap P.Priv)
  
parseExpr :: Text -> IO (Repr (Browse Name) K Name)
parseExpr t =
  throwLeftMy (parse (syntax <* Text.Parsec.eof) "myi" t)
  >>= throwLeftList . runCheck
  

-- | Load file as an expression.
runFile
  :: FilePath
  -> IO (Repr Assoc K (Nec Ident))
runFile file =
  T.readFile file
  >>= throwLeftMy . parse program' file
  >>= throwLeftList . runCheck . buildAbsParts
  >>= \ (pas, en, se, _) ->
    (pure . eval) ((Comps . val . Abs pas en) (Assoc se) `At` Key "run")
  
  
-- | Read-eval-print iteration
evalAndShow
  :: (Functor (b K), IsAssoc b) => Repr b K Name -> String
evalAndShow = showexpr . eval
  where
    showexpr :: Repr b K Name -> String
    showexpr a = case a of
      Prim (Number d)  -> show d
      Prim (Text t)    -> show t
      Prim (Bool  b)   -> show b
      Prim (IOError e) -> show e
      _                -> error "component missing: repr"
      

-- | Enter read-eval-print loop
browse
  :: IO ()
browse = first where
  first = readPrompt ">> " >>= rest

  rest ":q" = return ()
  rest s = parseExpr s >>= putStrLn . evalAndShow >> first
    
   
