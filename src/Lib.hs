{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}
module Lib
  ( displayProgram
  , runFile
  , loadFile
  , runExpr
  , loadExpr
  , browse
  , checkparams
  , ScopeError(..)
  , ExprError(..)
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
  
  
data ExprError = forall e. (Show e, Typeable e, MyError e) => ExprError e
  deriving Typeable
  

instance Show ExprError where
  show (ExprError e) = show e
  
instance MyError ExprError where
  displayError (ExprError e) = displayError e

    
substexpr
  :: (FilePath -> Either [ExprError] (Defns K (Expr K) (P.Vis Ident Key)))
  -> P.Expr (P.Name Ident Key FilePath)
  -> Either [ExprError] (Expr K a)
substexpr go e =
  first (ExprError <$>) (expr e)
    >>= getCollect . traverse (Collect . subst)
    >>= first (ExprError <$>) . checkparams . join
  where
    subst
      :: P.Name (Nec Ident) Key FilePath
      -> Either [ExprError] (Expr K (P.Vis Ident Key))
    subst (P.In (P.Priv (Nec Opt _))) = (pure . Block) (Defns [] M.empty)
    subst (P.In (P.Priv (Nec Req a))) = (pure . return) (P.Priv a)
    subst (P.In (P.Pub k)) = (pure . return) (P.Pub k)
    subst (P.Ex f) = Block <$> go f


substprogram
  :: (FilePath -> Either [ExprError] (Defns K (Expr K) Ident))
  -> P.Program FilePath
  -> Either [ExprError] (Defns K (Expr K) a)
substprogram go (P.Program m xs) = do
  b <- first (ExprError <$>) (program xs)
  let cb = traverse (Collect . subst) b <&> (>>>= id)
  b' <- getCollect (maybe id (liftA2 substenv . Collect . go) m cb)
  (first (ExprError <$>) . checkparams) (P.Priv <$> b')
  
  where
    subst :: P.Res (Nec Ident) FilePath -> Either [ExprError] (Expr K Ident)
    subst (P.In (Nec Opt _)) = (pure . Block) (Defns [] M.empty)
    subst (P.In (Nec Req a)) = pure (return a)
    subst (P.Ex f) = Block <$> go f
  
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
  -> Either [ExprError] (Defns K (Expr K) a)
substimports m = getimport where 
  m' = substprogram getimport <$> m
  
  getimport :: FilePath -> Either [ExprError] (Defns K (Expr K) a)
  getimport f = m' M.! f
       

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
    
   
