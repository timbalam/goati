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
    (parse (readsMy :: Parser P.Program) "myfmt" (T.pack s))
    
    
throwLeftMy
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either a b -> m b
throwLeftMy = either (throwM . MyExceptions . pure) return

throwLeftList
  :: (MyError a, Show a, Typeable a, MonadThrow m)
  => Either [a] b -> m b
throwLeftList = either (throwM . MyExceptions) return


data KeySource =
    File FilePath
  | User
  | Interpreter
  deriving (Eq, Ord, Show)

  
type K = Tag (KeySource, Int)


data ScopeError =
    FreeSym P.Symbol
  | FreeParam P.Var
  | ImportNotFound KeySource P.Import
  deriving (Eq, Show, Typeable)
  

instance MyError ScopeError where
  displayError (FreeParam v) = "Not in scope: Variable " ++ showMy v
  displayError (FreeSym s) = "Not in scope: Symbol " ++ showMy s
  displayError (ImportNotFound src i) =
    "Not found: Module " ++ showMy i ++ "\nIn :" ++ show src


-- | Imports
data SrcTree =
  SrcTree FilePath (Program Import) (M.Map Import SrcTree)
  
  
substImports :: SrcTree -> Either [ScopeError] (Defns k (Expr k) (Vis Ident a))
substImports (SrcTree file (Program mb xs) map) = do
  map' <- traverse substImports map
  let 
    subst :: Res a Import -> Expr k (Res a Import)
    subst =
      bitraverse return (\ i -> maybe (return i) Block (M.lookup i map'))
  
    xs' = (fmap . fmap) (>>= subst) xs
    
    cxs = first (ImportNotFound (File file) <$>) (traverse (traverse closed) xs')
    
  case mb of
    Nothing -> getCollect cxs >>= rec
    Just i -> (getCollect liftA2 env cxs . (maybe . collect) (pure i) pure)
      (M.lookup i map') >>= join
    
  where
    closed :: Traversable t => t (Res a Import) -> Collect [Import] (t a) 
    closed = traverse (\ k -> case k of
      In a -> pure a
      Ex i -> collect (pure i))
      
    env
      :: Monad m
      => NonEmpty (P.RecStmts a)
      -> Defns k (Expr k) (Vis Ident a)
      -> Either [ScopeError] (Defns k (Expr k) (Vis Ident a))
    env xs a@(Defns _ sea) = do
      b <- expr xs
      let
        e = Block a
        
        enb = M.mapMaybeWithKey (\ k _ -> case k of
          K_ _ -> Just (e `At` k)) sea
          
        subst l = fromMaybe (return l) (M.lookup l enb)
        
      return (b >>>= subst)
      



sourceFile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> m (M.Map Import (), SrcTree)
sourceFile file =
  liftIO (T.readFile file)
  >>= throwLeftMy . parse readsMy file
  >>= \ p -> do 
    (s, m) <- resolvetree dir (programimports p)
    return (s, SrcTree file p m)
  where
    dir = System.FilePath.dropExtension file
  

programimports :: P.Program Import -> M.Map Import ()
programimports = foldMap (flip M.singleton mempty)


sourceExpr
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> P.Syntax
  -> m (M.Map Import (), M.Map Import SrcTree)
sourceExpr dir = resolvetree dir . exprimports

  
exprimports :: P.Expr k (Res a Import) -> M.Map Import ()
exprimports = (foldMap . foldMap) (flip M.singleton mempty)
    
    
resolvetree
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> M.Map Import ()
  -> m (M.Map Import, M.Map Import SrcTree)
resolvetree dir s = loop s mempty mempty where

  loop x s m = do
    (xout, (sout, mout)) <- resolveImports dir x
    -- don't retry imports already tried in this directory
    let xout' = M.difference (M.difference xout s) m
    if M.null xout' then
      -- no new imports to resolve
      return (sout <> s, mout <> m)
    else do
      -- try to resolve inherited imports in this directory
      loop xout' (sout <> s) (mout <> m)
    
    
resolveimports
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> M.Map Import ()
  -> m (M.Map Import (), (M.Map Import (), M.Map Import SrcTree))
resolveimports dir = go where

  go s = do
    -- try to resolve imports in directory
    stry <- M.traverseWithKey (\ i () -> resolve dir i) s
    let 
      -- separate resolved imports
      (sout, spairs) = mapEither ((maybe . Left) () Right) stry
      
      -- combine inherited unresolved imports
      (nw, mout) = sequenceA spairs
      
    return (nw, (sout, mout))
      
  
resolve
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> Import
  -> m (Maybe (M.Map Import (), SrcTree))
resolve dir (Use l) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    sourceFile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
        
        
findimports
  :: (MonadIO m, MonadThrow m)
  => [FilePath]
  -> M.Map Import ()
  -> m (M.Map Import (), M.Map Import SrcTree)
findimports dirs s = loop s mempty where

  loop x s m = do
    (xout, (sout, mout)) <- findset dirs (mempty, (x, mempty))
    xout = M.difference (M.difference x s) m
    if M.null xout then
      return (sout <> s, mout <> m)
    else
      loop xout (sout <> s) (mout <> m)
      
  findset [] t = t
  findset (dir:dirs) x s m = do 
    (xout, (sout, mout)) <- resolveimports dir s
    findset dirs (x <> xout) sout (m <> mout)
      
  
    
      



data LoaderState a = LoaderState
  { imports :: M.Map FilePath a
  , searchPath :: [FilePath]
  }
  
  
newLoader :: [FilePath] -> LoaderState a
newLoader path = LoaderState { imports = M.empty, searchPath = path }


newtype Interpret b = Interpret (StateT (LoaderState ProgramL) IO b)
  deriving (Functor, Applicative, Monad, MonadState (LoaderState a), 
    MonadIO, MonadThrow)
  
  
type ProgramL =
  Program K (Either FilePath Import) (Res (Either FilePath Import) Ident)
  
  
sourceProgram
  :: FilePath -> Interpret ProgamL
sourceProgram file =
  liftIO T.readFile file
  >>= throwLeftMy . parse readsMy file
  >>= throwLeftList . resolve (File file) . program
  >>= bitraverse (resolveImport dir) (resolveImports dir)
  where
    dir = System.FilePath.dropExtension file
    
    
resolveImports
  :: (Traversable t)
  => FilePath
  -> t (Res (Either FilePath Import) a)
  -> Interpret (t (Res (Either FilePath Import) a))
resolveImports = traverse (\ v -> case v of
  Ex (Left _) -> return v
  Ex (Right m) -> maybe v Left <$> resolveImport m
  In _ -> return v)
    
    
resolveImport :: FilePath -> Import -> Interpret (Maybe FilePath)
resolveImport dir (Use l) = runMaybeT (MaybeT cached <|> MaybeT disk)
  where
    file = System.FilePath.normalise (dir </> T.unpack l <.> "my")
    
    cached = gets (M.lookup file)
    
    disk = do
      p <- liftIO (System.Directory.doesPathExist file)
      if p
      then 
        Just <$> (sourceProgram file >>= resolveImports dir >>= cache)
      else
        return Nothing
        
    cache b = state (\ s ->
      (b, s { imports = M.insert file b (imports s) }))
    

substImports
  :: LoaderState (Program K FilePath (Res FilePath Ident))
  -> LoaderState (Expr K Ident)
substImports s = s { imports = Block <$> m }
  where
    m = env <$> imports s
    
    subst file =
      fromMaybe (error ("resolveEnv: lookup: "++file)) (M.lookup file m)
    
    env
      :: Program K FilePath (Res FilePath Ident)
      -> Defns K (Expr K) Ident
    env (Program m b) =
      case m of
        Nothing -> b
        Just f -> b'
          where 
            b@(Defns _ se) = subst f
              
            en = M.mapMaybeWithKey (\ k -> case  k of
              Ident l -> Just (Block b `At` Ident l)
              _ -> Nothing) se
            
            b' = b >>>= \ v -> case v of
              Ex f -> Block (subst f)
              In l -> fromMaybe (return l) (M.lookup (Priv l) en))

  
closedImports
  :: Traversable t
  -> t (Res (Either FilePath Import) a)
  -> Either [ScopeError] (t (Res FilePath a))
closedImports = getCollect . traverse (\ v -> case v of
  Ex (Left f) -> pure (Ex f)
  Ex (Right m) -> collect [ImportNotFound m]
  In a -> pure (In a))
  
  
closedVar
  :: Traversable t
  => t (Res a P.Var)
  -> Either [ScopeError] (t a)
closedVar = getCollect . traverse (\ v -> case v of
  Ex a -> pure a
  In b -> collect [FreeParam b])
  
  
  
sourceExpr
  :: P.Syntax
  -> Interpret (Expr K (Res (Either FilePath Import) (Vis Ident P.Tag)))
sourceExpr =
  throwLeftList . resolve Interpreter . expr
    >=> sourceImports
    
    
sourceImports
  :: Traversable t
  => t (Res (Either FilePath Import) a)
  -> Interpret (t (Res (Either FilePath Import)) a)
sourceImports t = do
  p <- gets searchPath
  appEndoM (foldMap (EndoM . resolveImports) p) t
  
  
loadExpr :: P.Syntax -> Interpret (Expr K a)
loadExpr =
  sourceExpr
    >=> throwLeftList . closedImports
    >=> \ e -> gets (\ s -> e >>= `subst` substImports s)
    >=> throwLeftList . closedVar
  where
    subst (Ex file) = fromMaybe (error "loadExpr: file")
      . M.lookup file . imports
    subst (In a) = return a
  
  
evalAndPrint
  :: T.Text -> Interpret ()
evalAndPrint s = 
  throwLeftMy (parse (readsMy <* Text.Parsec.eof) "myi" s)
  >>= \ t -> liftIO System.Directory.getCurrentDirectory
  >>= \ cd -> localDir cd (loadExpr t)
  >>= (liftIO . putStrLn . show . eval :: Expr K Void -> Interpret ())


browse :: (MonadImport m, MonadIO m, MonadThrow m) => m ()
browse = first where
  first = liftIO (readPrompt ">> ") >>= rest

  rest ":q" = return ()
  rest s = evalAndPrint s >> first
  
  
runExpr :: FilePath -> P.Syntax -> IO (Expr K a)
runExpr dir s = interpret (loadExpr s) [dir]

      
runProgram :: [FilePath] -> FilePath -> IO (Expr K a)
runProgram dirs file =
  flip getField (Ident "run") . Block <$>
    interpret (loadProgram file >>= \ d -> (d >>>=) <$> substImport) dirs
  
  
  
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
    
   
