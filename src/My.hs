{-# LANGUAGE OverloadedStrings, GeneralizedNewtypeDeriving, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, ExistentialQuantification #-}

-- | Import system, parser and evaluator stage glue
module My
  ( displayProgram
  , runFile
  , loadFile
  , runExpr
  , loadExpr
  , browse
  , checkparams
  , checkimports
  , ScopeError(..)
  , ExprError(..)
  , module Types
  )
where

import My.Parser (Parser, parse, readsMy, ShowMy, showMy)
import My.Types.Error
import qualified My.Types.Parser as P
import My.Types
import My.Expr (program, expr)
import My.Eval (getField, eval)
import My.Import
import My.Util
import System.IO (hFlush, stdout, FilePath)
import Data.List.NonEmpty (NonEmpty(..), toList)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Bifunctor
import Data.Semigroup ((<>))
import Data.Maybe (fromMaybe)
import Data.Void
import Data.Typeable
import Control.Applicative (liftA2)
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

  
-- | Parse a string into the language grammar then back. 
--   Works like a formatter or (arguably) pretty printer.
displayProgram :: String -> String
displayProgram s =
  either
    displayError
    showMy
    (parse (readsMy :: Parser (P.Program P.Import)) "myfmt" (T.pack s))


-- | Error for an unbound parameter when closure checking and expression
data ScopeError = FreeParam (P.Vis Ident Key)
  deriving (Eq, Show, Typeable)
  

instance MyError ScopeError where
  displayError (FreeParam v) = "Not in scope: Variable " ++ showMy v
  
  
-- | Some MyError type
data ExprError = forall e. (Show e, Typeable e, MyError e) => ExprError e
  deriving Typeable
  
  
instance Show ExprError where
  show (ExprError e) = show e
  
instance MyError ExprError where
  displayError (ExprError e) = displayError e
  
    
-- | Traverse a syntax tree and substitute imported expressions.
--   
--   This stage runs after parsing and resolving all imports to files
substexpr
  :: (FilePath -> Either [ExprError] (Defns K (Expr K) (P.Vis Ident Key)))
  -- ^ File import function
  -> P.Expr (P.Name Ident Key FilePath)
  -- ^ Syntax tree with imports resolved to files
  -> Either [ExprError] (Expr K (P.Vis Ident Key))
  -- ^ Expression with imports substituted
substexpr go e =
  first (ExprError <$>) (expr e)
    >>= (join <$>) . getCollect . traverse (Collect . subst)
  where
    subst
      :: P.Name (Nec Ident) Key FilePath
      -> Either [ExprError] (Expr K (P.Vis Ident Key))
    subst (P.In (P.Priv (Nec Opt _))) = (pure . Block) (Defns [] M.empty)
    subst (P.In (P.Priv (Nec Req a))) = (pure . return) (P.Priv a)
    subst (P.In (P.Pub k)) = (pure . return) (P.Pub k)
    subst (P.Ex f) = Block <$> go f


-- | Traverse a program and substitute imported expressions 
substprogram
  :: (FilePath -> Either [ExprError] (Defns K (Expr K) Ident))
  -- ^ File import function
  -> P.Program FilePath
  -- ^ Program with resolved import files
  -> Either [ExprError] (Defns K (Expr K) (P.Vis Ident a))
  -- ^ Expression with imports substituted
substprogram go (P.Program m xs) = do
  b <- first (ExprError <$>) (program xs)
  let cb = traverse (Collect . subst) b <&> (>>>= id)
  (P.Priv <$>) <$> getCollect (maybe id (liftA2 substenv . Collect . go) m cb)
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


-- | Produce a expression for an import file, recursively substituting
--   nested imports
--
--   Partially apply with a map of resolved import files and parsed programs
--   for use as the first argument to 'substexpr' and 'substprogram'
substimports
  :: M.Map FilePath (P.Program FilePath)
  -- ^ Resolved import files and programs
  -> FilePath
  -- ^ File to import
  -> Either [ExprError] (Defns K (Expr K) a)
  -- ^ Expression with imports fully substituted
substimports m = getimport where 
  m' = (substprogram getimport >=> checkprogram) <$> m
  
  checkprogram = first (ExprError <$>) . checkparams
  
  getimport :: FilePath -> Either [ExprError] (Defns K (Expr K) a)
  getimport f = m' M.! f
       

-- | Check an expression for free parameters  
checkparams
  :: (Traversable t)
  => t (P.Vis Ident Key)
  -> Either [ScopeError] (t a)
checkparams = first (FreeParam <$>) . closed
  where
  closed :: Traversable t => t b -> Either [b] (t a)
  closed = getCollect . traverse (collect . pure)
 
    
-- | Load a file as an expression, using my language's import resolution
--   strategy (see 'findimports').
loadFile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -- ^ Source file
  -> [FilePath]
  -- ^ Import search path
  -> m (Defns K (Expr K) (P.Vis Ident Key))
  -- ^ Expression with imports substituted
loadFile f dirs = do
  (s, SrcTree f p m) <- sourcefile f
  (_, mm) <- findimports dirs s
  (m', p') <- throwLeftList (substpaths (File f) (m <> mm) p)
  throwLeftList (substprogram (substimports m') p')
    
    
-- | Load a file and evaluate the entry point 'run'.
runFile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -- ^ Source file
  -> [FilePath]
  -- ^ Import search path
  -> m (Expr K a)
  -- ^ Expression with imports substituted
runFile f dirs = (`getField` Key (K_ "run")) . Block
  <$> (loadFile f dirs >>= checkfile)
  where
    checkfile = throwLeftList . checkparams


-- | Produce an expression from a syntax tree.
loadExpr
  :: (MonadIO m, MonadThrow m)
  => P.Expr (P.Name Ident Key P.Import)
  -- ^ Syntax tree
  -> [FilePath]
  -- ^ Import search path
  -> m (Expr K (P.Vis Ident Key))
  -- ^ Expression with imports substituted
loadExpr e dirs = do
  (_, m) <- findimports dirs (exprimports e)
  (m', e') <- throwLeftList (sequenceA <$> (traverse (substpaths User m) e))
  throwLeftList (substexpr (substimports m') e')
  
  
-- | Produce and expression and evaluate entry point 'repr'.
runExpr :: (MonadIO m, MonadThrow m)
  => P.Expr (P.Name Ident Key P.Import)
  -- ^ Syntax tree
  -> [FilePath]
  -- ^ Import search path
  -> m (Expr K a)
  -- ^ Expression with imports substituted
runExpr e dirs = (`getField` Key (K_ "repr")) <$> (loadExpr e dirs >>= checkExpr)
  where
    checkExpr = throwLeftList . checkparams
  
  
-- | Read-eval-print iteration
evalAndPrint
  :: forall m. (MonadIO m, MonadReader [FilePath] m, MonadThrow m)
  => T.Text
  -- ^ Input text
  -> m ()
  -- ^ read-eval-print action
evalAndPrint s = 
  throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
  >>= \ t -> ask >>= runExpr t
  >>= (liftIO . putStrLn . show . eval :: MonadIO m => Expr K Void -> m ())


-- | Enter read-eval-print loop
browse
  :: [FilePath]
  -- ^ Import search path
  -> IO ()
  -- ^ Enter read-eval-print loop
browse = runReaderT first where
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
    
   
