{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving #-}
module Lib
  ( showProgram
  , runProgram
  , runImports
  , browse
  , module Types
  )
where

import Parser
  ( program
  , rhs
  )
import Types.Error
import qualified Types.Parser as Parser
import Types
import Expr( expr, closed )
import Eval( getField, eval )

import qualified Data.Map as M
import System.IO
  ( hFlush
  , stdout
  , FilePath
  )
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Bifunctor
import Control.Monad.State
import Text.Parsec.Text ( Parser )
import qualified Text.Parsec as P

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO (T.Text)
readPrompt prompt =
  flushStr prompt >> T.getLine

  
showProgram :: String -> String
showProgram s =
  either
    (displayError . ParseError)
    showMy
    (P.parse program "myi" (T.pack s))
    
    
throwLeftMy :: MyError a => Either a b -> IO b
throwLeftMy = either throwMy return

throwLeftList :: (MyError a, Foldable t, Functor t) => Either (t a) b -> IO b
throwLeftList = either throwList return
    
  
newtype ImpCache a m b = ImpCache (StateT (M.Map FilePath (Expr a)) m b)
  deriving (Functor, Applicative, Monad, MonadState (M.Map FilePath (Expr a)), MonadTrans, MonadIO)
  
  
evalImpCache :: Monad m => ImpCache a m b -> m b
evalImpCache (ImpCache s) = evalStateT s M.empty
  
  
lookupCache :: FilePath -> ImpCache a IO (Expr a)
lookupCache file = gets (M.lookup file) >>= \ m -> case m of
    Just e -> return e
    Nothing -> do
      e <- loadProgram file
      modify' (M.insert file e)
      return e
    
    
loadProgram :: FilePath -> ImpCache a IO (Expr a)
loadProgram file =
  lift (T.readFile file
    >>= throwLeftMy . first ParseError . P.parse program file
    >>= throwLeftList . expr . flip Parser.Block Nothing . toList
    >>= throwLeftList . closed)
  >>= loadImports
  
  
loadImports :: Expr (Sym a) -> ImpCache a IO (Expr a)
loadImports = fmap join . traverse (\ e -> case e of
  Intern a -> return (return a)
  Extern file -> lookupCache file)
  
  
runImports :: Expr (Sym a) -> IO (Expr a)
runImports = evalImpCache . loadImports
      
      
runProgram :: FilePath -> IO (Expr a)
runProgram file =
  evalImpCache (loadProgram file)
  >>= throwLeftMy . flip getField (Label "run")

  
evalAndPrint :: T.Text -> ImpCache Vid IO ()
evalAndPrint s =
  lift ((throwLeftMy . first ParseError) (P.parse (rhs <* P.eof) "myi" s)
    >>= throwLeftList . expr
    >>= throwLeftList . closed)
  >>= loadImports
  >>= lift . throwLeftMy . eval
  >>= (lift . putStrLn . showMy :: MonadTrans t => Expr Vid -> t IO ())


browse :: IO ()
browse = evalImpCache first where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
   
