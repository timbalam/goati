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
import Expr( program, expr, MonadResolve(..) )
import Eval( getField, eval )
import Util

import System.IO
  ( hFlush
  , stdout
  , FilePath
  )
import qualified System.FilePath
import System.FilePath( (</>), (<.>) )
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
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.RWS
import Control.Monad.Trans.Maybe
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
    (parse (readsMy :: Parser P.Program) "myi" (T.pack s))
    
    
throwLeftMy
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either a b -> m b
throwLeftMy = either (throwM . MyExceptions . pure) return

throwLeftList
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either [a] b -> m b
throwLeftList = either (throwM . MyExceptions) return


-- | Concrete resolve instance
data KeySource =
    File FilePath
  | User
  | Interpreter
  deriving (Eq, Ord, Show)

  
type K = Key (KeySource, Int)


data ScopeError =
    FreeSym P.Symbol
  | FreeParam P.Var
  | ImportNotFound P.Import
  | CyclicImport FilePath
  deriving (Eq, Show, Typeable)
  

instance MyError ScopeError where
  displayError (FreeParam v) = "Not in scope: Variable " ++ showMy v
  displayError (FreeSym s) = "Not in scope: Symbol " ++ showMy s
    
    
data Symctx = Symctx
  { next :: Int
  , unbound :: M.Map P.Symbol Int
  }
  
  
newsymctx = Symctx 0 M.empty
    
    
resolve
  :: KeySource 
  -> ReaderT KeySource (State Symctx) a
  -> Either [ScopeError] a
resolve file m = if null errors then return a else Left errors
  where 
    (a, s) = runState (runReaderT m file) newsymctx
    
    errors = FreeSym <$> M.keys (unbound s)
  
    
instance MonadResolve (KeySource, Int) (ReaderT (Maybe FilePath) (State Symctx)) where
  resolveSymbol s = do
    mi <- gets (M.lookup s . unbound)
    file <- ask
    case mi of
      Just i -> return (file, i)
      Nothing -> state (\ Symctx i m ->
        ((file, i), Symctx (i+1) (M.insert s i m)) 
        )
      
  localSymbols s m = do
    file <- ask
    state (\ ctx ->
      let 
        ss = S.fromList s
        (sx, rx) = M.partitionWithKey (\ k _ -> k ` member` ss) (unbound ctx)
        (a, ctx') = runState (runReaderT m file) (ctx {unbound = rx })
      in
        (a, ctx' { unbound = sx `M.union` M.withoutKeys (unbound ctx') ss }))
    


-- | Imports
class MonadImport m where
  resolveImport :: Import -> m (Maybe (FilePath, Defns K (Expr K) FilePath))
   
  localDir :: FilePath -> m a -> m a
  
  instantiateImports :: Defns K (Expr K) FilePath -> m (Defns K (Expr K) a)
  
  
loadProgram
  :: (MonadIO m, MonadImport m, MonadThrow m)
  => FilePath
  -> m (Defns K (Expr K) FilePath)
loadProgram file =
  liftIO T.readFile file
  >>= throwLeftMy . parse readsMy file
  >>= throwLeftList . resolve (File file) . program
  >>= \ (m, b) -> localDir (System.FilePath.dropExtension file) (do
    b' <- resolveImports (File file) b
    case m of
      Nothing -> return b'
      Just m -> do
        (f, Defns _ se) <- resolveImport m
        let
          en = M.mapMaybeWithKey (\ k -> case  k of
            Priv _ -> Just (Var f `At` k)
            Pub _ -> Nothing) se
          
        return (b' >>>= \ v -> case v of
          Ex _ -> return v
          In (Priv l) -> fromMaybe (return v) (M.lookup (Priv l) en)
          In (Pub _) -> return v))
  >>= throwLeftList . closedVar

  
closedVar
  :: Traversable t
  => t (Res a (Vis Ident K))
  -> Either [ScopeError] (t a)
closedVar = getCollect . traverse (\ v -> case v of
  Ex a -> pure a
  In b -> collect [FreeParam b])
      
  
resolveImports
  :: (Traversable t, MonadIO m, MonadImport m, MonadThrow m)
  => KeySource
  -> t (Res Import a)
  -> m (t (Res FilePath a))
resolveImports file = traverse (\ v -> case v of
  Ex m -> resolveImport m <&> (\ mb -> case mb of
    Nothing -> collect [ImportNotFound m]
    Just f
      | File f == file -> collect [CyclicImport f]
      | otherwise -> Left (Ex f))
  In a -> (pure . pure) (In a))
    >=> throwLeftList . getCollect . sequenceA
    
  
  
sourceExpr :: (MonadImport m, MonadIO m, MonadThrow m) => P.Syntax -> m (Expr K a)
sourceExpr =
  throwLeftList . resolve Interpreter . expr
    >=> resolveImports Interpreter
    >=> throwLeftList . closedVar
    >=> instantiateImports
  
  
evalAndPrint
  :: forall m. (MonadImport m, MonadIO m, MonadThrow m)
  => T.Text -> m ()
evalAndPrint s = 
  throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
  >>= \ t -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> localDir cd (sourceExpr t)
  >>= (liftIO . putStrLn . show . eval :: Expr K Void -> m ())


browse :: (MonadImport m, MonadIO m) => m ()
browse = first where 
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first


-- | Concrete import instance
data LoaderState = LoaderState
  { imports :: M.Map FilePath (Defns K (Expr K) FilePath)
  , searchPath :: [FilePath]
  }
  
  
newLoader :: [FilePath] -> LoaderState
newLoader path = LoaderState { imports = M.empty, searchPath = path }


interpret :: ReaderT [FilePath] (StateT LoaderState IO) a -> [FilePath] -> IO a
interpret s path = evalStateT (runReaderT s path) (newLoader [])

  
loadImport
  :: (MonadState LoaderState m, MonadImport m, MonadIO m)
  => FilePath
  -> m (Maybe (Defns K (Expr K) FilePath))
loadImport file = runMaybeT (MaybeT cached <|> MaybeT disk)
  where
    file' = System.FilePath.normalise file
    
    cached = gets (M.lookup file' . imports)
    
    disk = do
      p <- liftIO (System.Directory.doesPathExist file')
      if p then Just <$> (loadProgram file' >>= cache) else return Nothing
        
    cache
      :: MonadState LoaderState m
      => Defns K (Expr K) FilePath
      -> m (Defns K (Expr K) FilePath)
    cache b = do
      modify' (\ s -> s { imports = M.insert file' b (imports s) })
      return b
  

instance MonadImport (ReaderT [FilePath] (StateT LoaderState IO)) where
  resolveImport (Use l) = do
    files <- asks ((</> (T.unpack l <.> "my")) <$>) 
    (runMaybeT . asum) 
      [ (,) file <$> MaybeT (loadImport file) | file <- files ]
        
  localDir dir = local (++[dir])
  
  instantiateImports b = do
    m <- gets imports
    let
      m' = inst <$> m
      
      inst :: Defns K (Expr K) FilePath -> Defns K (Expr K) a
      inst b = b >>>= 
        maybe (error "instantiateImports") Block . flip M.lookup m'
    return (inst b)
  
  
runSource :: FilePath -> P.Syntax -> IO (Expr K a)
runSource dir s = interpret (sourceExpr s) [dir]

      
runProgram :: [FilePath] -> FilePath -> IO (Expr K a)
runProgram dirs file =
  flip getField (Ident "run") . Block <$>
    interpret (loadProgram file >>= instantiateImports) dirs
  
  
  
-- | Alternative resolve implementation
data Varctx = Varctx
  { symbols :: M.Map P.Symbol Int
  , source :: KeySource
  }
  
 
newVarctx :: KeySource -> Varctx
newVarctx = Varctx M.empty


symlookup :: P.Symbol -> Varctx -> Maybe Int
symlookup s = M.lookup s . symbols


symlocal :: MonadState Int m => [P.Symbol] -> m (Varctx -> Varctx)
symlocal s = do 
  s' <- newset s
  return (\ ctx -> ctx { symbols = s' `M.union` symbols ctx })

  
new :: (MonadState i m, Enum i) => m i
new = state (\ i -> (succ i, i))


newset :: (MonadState i m, Enum i, Ord k) => [k] -> m (M.Map k i)
newset = sequenceA . M.fromSet (const new) . S.fromList


resolve'
  :: KeySource
  -> MaybeT (RWS Varctx [P.Symbol] Int) a
  -> Either [ScopeError] a
resolve' file m = maybe (Left errors) Right ma
  where
    (ma, ls) = evalRWS (runMaybeT m) (newVarctx file) 0
    
    errors = FreeSym <$> nub ls
    
    
instance MonadResolve (KeySource, Int) (MaybeT (RWS Varctx [P.Symbol] Int)) where
  resolveSymbol s = MaybeT (do 
    mk <- asks (\ ctx -> Symbol . (,) (source ctx) <$> symlookup s ctx)
    maybe (tell [s] >> return Nothing) (return . Just) mk) -- log missing lookups
  
  localSymbols s = mapMaybeT (\ m -> do
    f <- symlocal s
    local f m)
    
   
