{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}

-- | Module containing logic for resolving import names to paths
--
-- Goat allows code to be imported using '@use'.
-- An import '@use modname' resolves to the code for module 'modname'.
--
-- A Goat file can have a preface with an '@import' section,
-- where files can be associated with module names via a set of 'modname = ../path/to/file.gt;' statements.
-- 
-- Preface sections are optional,
-- and do not need to define all module names used. 
-- Unassociated module names in an imported file will be associated to the same names of the importing file.
--
-- The Goat interpreter will in the last case try to resolve any unassociated names in the entry file
-- (for instance using a configuration file of installed packages),
-- and error on unassociated names.

module Goat.Syntax.Import
  ( 
  )
where

import Goat.Syntax.Class
import Goat.Syntax.Syntax (Import(..))
import Goat.Syntax.Parser (program, parse)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Typeable (Typeable)
import qualified Data.Map as M
import Data.Bifunctor (first)
import Data.Bitraversable (bitraverse)
import Data.Semigroup (Semigroup(..))
import Data.String (IsString(..))
import Control.Applicative (liftA2)
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Free (MonadFree(..))
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))


data Mod k f = Mod [Ident] [StaticError k] (Repr f)

moduleError :: ImportError -> Mod k (Dyn k f)
moduleError e =
  (Module [] [StaticError e']
    . pure
    . Repr
    . Block
    . const)
    (throwDyn e')
  where
    e' = ImportError e
    
includeMod
 :: [Ident]
 -> ReaderT ([Ident], [[S.Ident]]) (Writer [StaticError k])
      (Eval (Dyn k f))
 -> Reader [Mod (Dyn k f)] (Mod (Dyn k f))
 -> ReaderT [Ident] (Writer [ImportError])
      (Reader [Mod (Dyn k f)] (Mod (Dyn k f)))
includeMod ks' res mod = reader (\ ns ->
  do
    Module ks es r <- mod
    mods <- ask
    let
      rs = map (r #.) ks
      (ees, ev) = runRes res ns [ks]
      r' = runEval ev mods [rs]
    return (Module ks' (es++ees) r'))
 
 
newtype Include k f =
  Include (ReaderT [Ident] (Writer [ImportError])
    (Reader [Mod k f] (Mod k f)))

instance Include (Include k (Dyn k f)) where
  type Inc (Include k (Dyn k f)) = Module k (Dyn k f)
  include_ n (Module ks a) = Include
    (asks (handleUse n)
      >>= maybe
        (tell [e] >> return (pure (moduleError e)))
        (return . reader)
      >>= applyMod ks a)
    where
      e = NotModule n

      
newtype Module k f = Module [Ident] (Res k (Eval f))

instance Module (Module k (Dyn k f)) where
  type ModuleStmt (Module k (Dyn k f)) =
    Names (Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      ))
  module_ rs = Module ks (block_ rs)
    where
      (ks, rs') = foldMap (\ (Names ks r) -> (ks, [r]) rs


newtype Src a = Src (Reader (M.Map FilePath a) (M.Map Ident a))

  

-- | Parse a source file and find imports
sourcefile
 :: FilePath -> StateT (M.Map FilePath (Include Ident (DynIO Ident))) IO (Include Ident (DynIO Ident))
sourcefile file = do
  cache <- get
  maybe
    (do 
      T.readFile file >>= 
    return
    (M.lookup file cache)
  where
    notfound = do
      t <- liftIO (T.readFile file)
        <- runExtern (parse program file t)
    

-- | Find and import dependencies for a source
sourcedeps :: (MonadIO m, MonadThrow m, Deps r) => [FilePath] -> Src r a -> m (Src r a)
sourcedeps dirs (Src (y, k)) = do
  (unres, res) <- findimports dirs y
  (return . Src) (unres, k . substres res)
  where
    substres :: M.Map Import (M.Map Import r -> r) -> M.Map Import r -> M.Map Import r
    substres res m = m' 
      where
        m' = M.map ($ M.union m' m) res
                
       
-- | Traverse to check for unresolved imports.
checkimports :: Src r a -> Either [ImportError] a
checkimports (Src (y, k)) = 
  k <$> getCollect (M.traverseWithKey (\ k f -> (collect . pure) (ImportNotFound f k)) y)
        
        
-- | Process some imports
data Process a b = Proc
  { left :: M.Map Import a
  , done :: b
  }
        
-- | Find files to import.
--
--   Try to resolve a set of imports using a list of directories, recursively
--   resolving imports of imported source files.
findimports
  :: (MonadIO m, MonadThrow m, Deps r)
  => [FilePath]
  -- ^ Search path
  -> M.Map Import KeySource
  -- ^ Set of imports to process
  -> m (M.Map Import KeySource, M.Map Import (M.Map Import r -> r))
  -- ^ Sets of imports resolved to source files
findimports dirs y = loop (Proc { left = y, done = mempty }) where

  -- | Try to resolve a set of imports by iterating over a set of source 
  --   directories. Repeat with any new unresolved imports discovered during a 
  --   pass.
  loop
    :: (MonadIO m, MonadThrow m, Deps r)
    => Process KeySource (M.Map Import KeySource, M.Map Import (M.Map Import r -> r))
    -- ^ Process imports in this pass
    -> m (M.Map Import KeySource, M.Map Import (M.Map Import r -> r))
    -- ^ Final sets of unresolved and resolved imports
  loop search = do
    -- Make a resolution pass over search path
    (newunres, srcs) <- findset dirs (left search)
    
    let
      -- Determine new set of unresolved imports depended by resolved imports
      (unp, newres) = traverse getSrc srcs
      -- Already processed imports
      (oldunres, oldres) = done search
      unres = M.union oldunres newunres
      res = M.union oldres newres
      p = (unres, res)
      -- Filter imports that have already been processed on search path
      unp' = M.difference (M.difference unp unres) res
    if M.null unp' then
      -- No unprocessed imports to resolve
      return p
    else
      -- New pass over search path to try to resolve new set of imports
      loop (Proc { left = unp, done = p })
  
  -- | Loop over a list of directories to resolve a set of imports keeping
  --   track of any new unresolved imports that arise.
  findset
    :: (MonadIO m, MonadThrow m, Deps r)
    => [FilePath]
    -- ^ Remaining search path
    -> M.Map Import a
    -- ^ Imports to be resolved
    -> m (M.Map Import a, M.Map Import (Src r r))
    -- ^ Resolved imports after loop
  findset dirs y = loop dirs (Proc { left = y, done = mempty }) where
    loop
      :: (MonadIO m , MonadThrow m, Deps r)
      => [FilePath]
      -> Process a (M.Map Import (Src r r))
      -> m (M.Map Import a, M.Map Import (Src r r))
    loop [] search = return (left search, done search)
    loop (dir:dirs) search = do 
      (unres, res) <- resolveimports dir (left search)
      loop dirs (Proc { left = unres, done = (done search <> res) })
    
    
-- | Attempt to resolve a set of imports to files of directory.
resolveimports
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -> M.Map Import a
  -> m (M.Map Import a, M.Map Import (Src r r))
resolveimports dir set = do
  tried <- M.traverseWithKey (\ i a -> maybe (Left a) Right <$> resolve dir i) set
   -- Unresolved 'Left', resolved imports 'Right'.
  return (M.mapEither id tried)
      
  
-- | Attempt to resolve an import in a directory.
--
--   For an import 'name' looks for a file 'name.my'.
resolve
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -- ^ Directory to search
  -> Import
  -- ^ Import name
  -> m (Maybe (Src r r))
  -- ^ May return a pair of a set of nested unresolved imports and a import
  -- source tree if import can be resolved.
resolve dir (Use (I_ l)) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    Just <$> sourcefile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
