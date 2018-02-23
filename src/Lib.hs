{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
module Lib
  ( displayProgram
  , runFile
  , loadFile
  , runExpr
  , loadExpr
  , browse
  , checkparams
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
import Data.List.NonEmpty( NonEmpty(..), toList )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bifunctor
import Data.Semigroup( (<>) )
--import Data.Foldable( asum )
import Data.Maybe( fromMaybe )
import Data.Void
import Data.Typeable
import Control.Applicative( liftA2 )
import Control.Monad.Reader
import Control.Monad.Catch
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
    (parse (readsMy :: Parser (P.Program P.Import)) "myfmt" (T.pack s))


data ScopeError = FreeParam (P.Vis Ident Key)
  deriving (Eq, Show, Typeable)
  

instance MyError ScopeError where
  displayError (FreeParam v) = "Not in scope: Variable " ++ showMy v

    
substexpr
  :: (FilePath -> Either [ScopeError] (Defns K (Expr K) (P.Vis Ident Key)))
  -> P.Expr (P.Name Ident Key FilePath)
  -> Either [ScopeError] (Expr K a)
substexpr go e =
  expr e
    >>= getCollect . traverse subst
    >>= checkparams . join
  where
    subst
      :: P.Name (Nec Ident) Key FilePath
      -> Collect [ScopeError] (Expr K (P.Vis Ident Key))
    subst (P.In (P.Priv (Nec Opt _))) = (pure . Block) (Defns [] M.empty)
    subst (P.In (P.Priv (Nec Req a))) = (pure . return) (P.Priv a)
    subst (P.In (P.Pub k)) = (pure . return) (P.Pub k)
    subst (P.Ex f) = Block <$> Collect (go f)


substprogram
  :: (FilePath -> Either [ScopeError] (Defns K (Expr K) Ident))
  -> P.Program FilePath
  -> Either [ScopeError] (Defns K (Expr K) a)
substprogram go (P.Program m xs) = do
  b <- program xs
  let cb = traverse subst b <&> (>>>= id)
  b' <- getCollect (maybe id (liftA2 substenv . Collect . go) m cb)
  checkparams (P.Priv <$> b')
  
  where
    subst :: P.Res (Nec Ident) FilePath -> Collect [ScopeError] (Expr K Ident)
    subst (P.In (Nec Opt _)) = (pure . Block) (Defns [] M.empty)
    subst (P.In (Nec Req a)) = pure (return a)
    subst (P.Ex f) = Block <$> Collect (go f)
  
    substenv
      :: Defns K (Expr K) Ident
      -> Defns K (Expr K) Ident
      -> Defns K (Expr K) Ident
    substenv a@(Defns _ se) = (>>>= enlookup)
      where
        en :: M.Map K (Expr K Ident)
        en = M.mapMaybeWithKey (\ k _ -> case k of
          Key _ -> Just (Block a `At` k)
          _ -> Nothing) se
          
        enlookup a = fromMaybe (return a) ((M.lookup . Key) (K_ a) en)


substimports
  :: M.Map FilePath (P.Program FilePath)
  -> FilePath
  -> Either [ScopeError] (Defns K (Expr K) a)
substimports m = getimport where 
  m' = substprogram getimport <$> m
  
  getimport :: FilePath -> Either [ScopeError] (Defns K (Expr K) a)
  getimport f = (fromMaybe . error) ("substimports: " ++ show f) (M.lookup f m')
       

checkparams
  :: (Traversable t)
  => t (P.Vis Ident Key)
  -> Either [ScopeError] (t a)
checkparams = first (FreeParam <$>) . closed
  where
  closed :: Traversable t => t b -> Either [b] (t a)
  closed = getCollect . traverse (collect . pure)
 
    
loadFile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> [FilePath]
  -> m (Defns K (Expr K) a)
loadFile f dirs = do
  (s, SrcTree f p m) <- sourcefile f
  (_, mm) <- findimports dirs s
  (m', p') <- throwLeftList (substpaths (File f) (m <> mm) p)
  throwLeftList (substprogram (substimports m') p')
    
    
runFile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> [FilePath]
  -> m (Expr K a)
runFile f dirs = (`getField` Key (K_ "run")) . Block <$> loadFile f dirs



loadExpr
  :: (MonadIO m, MonadThrow m)
  => P.Expr (P.Name Ident Key P.Import)
  -> [FilePath]
  -> m (Expr K a)
loadExpr e dirs = do
  (_, m) <- findimports dirs (exprimports e)
  (m', e') <- throwLeftList (sequenceA <$> (traverse (substpaths User m) e))
  throwLeftList (substexpr (substimports m') e')
  
  
runExpr :: (MonadIO m, MonadThrow m)
  => P.Expr (P.Name Ident Key P.Import)
  -> [FilePath]
  -> m (Expr K a)
runExpr e dirs = (`getField` Key (K_ "repr")) <$> loadExpr e dirs
  
  
evalAndPrint
  :: forall m. (MonadIO m, MonadReader [FilePath] m, MonadThrow m)
  => T.Text -> m ()
evalAndPrint s = 
  throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
  >>= \ t -> ask >>= runExpr t
  >>= (liftIO . putStrLn . show . eval :: MonadIO m => Expr K Void -> m ())


browse :: [FilePath] -> IO ()
browse = runReaderT first where
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
    
   
