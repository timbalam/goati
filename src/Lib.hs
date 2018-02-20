{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
module Lib
  ( displayProgram
  , runProgram
  , runSource
  , browse
  , interpret
  , source
  , K
  , closed
  , resolve
  , ScopeError(..)
  , module Types
  )
where

import Parser
  ( Parser
  , parse
  , readsMy
  , ShowMy
  , showMy
  )
import Types.Error
import qualified Types.Parser as P
import Types
import Expr( program, expr )
import Eval( getField, eval )
import Import
import Util

import System.IO
  ( hFlush
  , stdout
  , FilePath
  )
import qualified System.Directory
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bifunctor
import Data.Foldable( asum )
import Data.Maybe
import Data.Void
import Data.List( union, elemIndex, nub, (\\) )
import Data.Typeable
import Control.Applicative( liftA2, Alternative(..) )
--import Control.Monad.State
import Control.Monad.Reader
--import Control.Monad.Trans.Maybe
import Control.Monad.Catch
--import Text.Parsec.Text ( Parser )
import qualified Text.Parsec

  
-- Console / Import --
flushStr :: T.Text -> IO ()
flushStr s =
  T.putStr s >> hFlush stdout

  
readPrompt :: T.Text -> IO (T.Text)
readPrompt prompt =
  flushStr prompt >> T.getLine

  
displayProgram :: String -> String
displayProgram s =
  either
    displayError
    showMy
    (parse (readsMy :: Parser P.Program) "myfmt" (T.pack s))
    
    
throwLeftMy
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either a b -> m b
throwLeftMy = either (throwM . MyExceptions . pure) return

throwLeftList
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either [a] b -> m b
throwLeftList = either (throwM . MyExceptions) return




data ScopeError =
    FreeParam P.Var
  | ImportNotFound KeySource P.Import
  deriving (Eq, Show, Typeable)
  

instance MyError ScopeError where
  displayError (FreeParam v) = "Not in scope: Variable " ++ showMy v
  displayError (ImportNotFound src i) =
    "Not found: Module " ++ showMy i ++ "\nIn :" ++ show src

    
substexpr
  :: (FilePath -> Either [ScopeError] (Defns K (Expr K) a))
  -> P.Expr (Res P.Var FilePath)
  -> Either [ScopeError] (Expr K a)
substexpr go e =
  (join <$> expr e >>= traverse subst)
    >>= checkparams
  where
    subst :: Res a FilePath -> Either [ScopeError] (Expr K a)
    subst (In a) = pure (return a)
    subst (Ex f) = go f


substprogram
  :: (FilePath -> Either [ScopeError] (Defns K (Expr K) a))
  ->  P.Program FilePath
  ->  Either [ScopeError] (Defns K (Expr K) a)
substprogram go (P.Program m xs) =
  ((>>>= id) <$> program xs >>= traverse subst)
    >>= (checkparams <=< maybe pure substenv m)
  where
    subst :: Res a FilePath -> Either [ScopeError] (Expr K a)
    subst (In a) = pure (return a)
    subst (Ex f) = go f
  
    substenv
      :: (Bound t, Traversable t (Expr K))
      => FilePath -> t Ident -> Either [ScopeError] (t (Expr K) Ident)
    substenv f b = do
      a@(Defns _ se) <- go f
      let
        en = M.mapMaybeWithKey (\ k -> case  k of
          K_ _ -> Just (Block a `At` k)
          _ -> Nothing) se
          
        enlookup a = (fromMaybe . pure) (return a) (M.lookup (K_ a) en)
            
      traverse enlookup b >>>= id



substimports
  :: M.Map FilePath (P.Program FilePath)
  -> FilePath
  -> Either [ScopeError] (Defns K (Expr K) a)
substimports m = getimport where 
  m' = substprogram getimport <$> m
  
  getimport :: FilePath -> Either [ScopeError] (Defns K (Expr K) a)
  getimport f = (fromMaybe . error) ("substimports: " ++ show f) (M.lookup f m')
       

checkparams :: Traversable t => t Ident -> Either [ScopeError] (t a)
checkparams = first (FreeParam . Priv <$>) . closed
  where
  closed :: Traversable t => t b -> Either [b] (t a)
  closed = getCollect . traverse (collect . pure)
 
    
loadfile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> [FilePath]
  -> m (Defns K (Expr K) a)
loadfile f dirs = do
  (s, SrcTree f p m) <- sourcefile f
  (s', m') <- findimports dirs s
  throwLeftList (do
    (m'', p'') <- (substpaths p) (m <> m')
    substprogram (substimports m'') p'')


loadexpr
  :: (MonadIO m, MonadThrow m)
  => P.Expr (Res P.Var Import)
  -> [FilePath]
  -> m (Expr K a)
loadexpr e dirs = do
  (_, m) <- findimports dirs (exprimports e)
  throwLeftList (do 
    (m', e') <- sequenceA <$> (traverse substpaths m)
    substexpr (substimports m') e')
  
  
evalAndPrint
  :: (MonadIO m, MonadReader [FilePath] m, MonadThrow m)
  => T.Text -> m ()
evalAndPrint s = 
  throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
  >>= \ t -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> localDir cd (ask >>= loadexpr t)
  >>= (liftIO . putStrLn . show . eval :: Expr K Void -> m ())


browse :: (MonadReader [FilePath] m, MonadIO m, MonadThrow m) => m ()
browse = first where
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first

      
runfile :: FilePath -> [FilePath] -> IO (Expr K a)
runfile file dirs =
  (`getField` Key (K_ "run")) . Block <$> loadfile file dirs
    
   
