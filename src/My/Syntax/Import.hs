-- | Module containing logic for resolving import names to paths
--
--   My language imports are declared using '@use'. An import '@use modname' in 
--   a file 'code.my' will resolve to a source file 'code/modname.my' in a sibling 
--   'code' subdirectory if the file exists.
--
--   An unresolved import can also be resolved by a parent import, for example, if
--   'code/modname.my' exists and imports '@use submodname', then by default a 
--   source file 'code/modname/submodname.my' is looked for. If no such file
--   exists, then the importing file 'code.my' can resolve the import to a file 
--   in its module directory 'code/submodname.my'. 
--
--   In effect, we have something like directory-scoped local imports, where 
--   nested files can import code from parent directories up to a root directory 
--   that corresponds to an 'entry point' i.e. a library or application source 
--   folder, or the current directory for a repl.
--
--   A list of entry points can be provided via 'findimports' allowing library 
--   code to be imported.

module My.Import
  ( substpaths
  , sourcefile
  , programimports
  , exprimports
  , findimports
  , checkimports
  , SrcTree(..)
  --, Process(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Interpreter (KeySource(..))
import qualified My.Types.Classes
import My.Parser (showMy, readsMy, parse)
import My.Util (Collect(..), collect)
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Typeable (Typeable)
import Data.Bifunctor (first)
import Data.Bitraversable (bitraverse)
import Data.Semigroup ((<>))
import Control.Applicative (liftA2)
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.IO.Class (MonadIO(..))


-- | Summarises a source file and resolved imports.
--
--   A import source tree describes a source file, and a set of
--   transitive imports that are resolved to files in the file's
--   'module' directory (which is the 
data SrcTree =
  SrcTree
    FilePath
    -- ^ Source file name
    (P.Program P.Import)
    -- ^ Program code
    (M.Map P.Import SrcTree)
    -- ^ Imported names and resolved sources
  
  
-- | Error when an import name cannot be resolved to a source file.
data ImportError = ImportNotFound KeySource P.Import
  deriving (Eq, Show, Typeable)
  

instance My.Types.Classes.MyError ImportError where
  displayError (ImportNotFound src i) =
    "Not found: Module " ++ showMy i ++ "\nIn :" ++ show src
     
      
-- | Given a 'KeySource' label, a map of imported source trees, and a source
--   expression, traverses the expression and tree of imported sources and
--   substitutes all import names with resolved files, and returns both the
--   full set of imported files and corresponding programs, and the input 
--   expression with import file names substituted.
substpaths
  :: Traversable t
  => KeySource
  -- ^ Label for input source
  -> M.Map P.Import SrcTree
  -- ^ Maps import names to source trees
  -> t P.Import
  -- ^ Expression with import names
  -> Either [ImportError] (M.Map FilePath (P.Program FilePath), t FilePath)
  -- ^ Flattened map of all imported files to program code, and
  --   input expression, with all imports resolved to files
substpaths file m p = (getCollect . bitraverse
  (M.traverseWithKey (checkimports . File))
  (checkimports file))
  (go p m)
  where
  
    -- | Recursively get imported files from source tree.
    --
    --   Substitutes any unresolved imports from nested sources and the
    --   current expression that are resolved for the current source.
    --   This produces a form of directory level scoping of imports, for 
    --   directories below the entry point - e.g. main file or repl current 
    --   directory.
    go
      :: Functor f
      => f P.Import
      -> M.Map P.Import SrcTree
      -> (M.Map FilePath (P.Program (Either FilePath P.Import)),
        f (Either FilePath P.Import))
    go p m = (((>>= subst m) <$>) <$> flatimports m, subst m <$> p)
    
    -- | Substitute a named import with the resolved source file name.
    subst :: M.Map P.Import SrcTree -> P.Import -> Either FilePath P.Import
    subst m i = maybe (Right i) (\ (SrcTree f _ _) -> Left f) (M.lookup i m)
    
    -- | Traverse import source tree and collect imported files.
    flatimports
      :: M.Map P.Import SrcTree
      -> M.Map FilePath (P.Program (Either FilePath P.Import))
    flatimports m = M.fromList (M.elems m') <> s where
      (s, m') = traverse (\ (SrcTree f p m) -> (,) f <$> go p m) m
        
       
-- | Traverse to check for unresolved imports.
checkimports
  :: Traversable t
  => KeySource
  -> t (Either a P.Import)
  -> Collect [ImportError] (t a)
checkimports file p = first (ImportNotFound file <$>) (closed p)
  where
  closed :: Traversable t => t (Either a b) -> Collect [b] (t a)
  closed = traverse (\ k -> case k of
    Left f -> pure f
    Right i -> collect (pure i))
  

-- | Parse a source file and find imports
sourcefile
  :: (MonadIO m, MonadThrow m, C.Program r)
  => FilePath
  -> m (M.Map P.Import (), SrcTree)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse program file
  >>= \ r -> do 
    (unres, res) <- findimports [dir] (programimports r)
    return (unres, SrcTree file p res)
  where
    dir = System.FilePath.dropExtension file
  

-- | Set of named imports in a program
programimports :: C.Program r => r -> M.Map P.Import ()
programimports = foldMap (flip M.singleton mempty)

  
-- | Set of named imports in a syntax tree
exprimports :: P.Expr (P.Res a P.Import) -> M.Map P.Import ()
exprimports = (foldMap . foldMap) (flip M.singleton mempty)
        
        
-- | Process some imports
data Process a = Proc
  { left :: M.Map P.Import ()
  , done :: a
  }
  
        
-- | Find files to import.
--
--   Try to resolve a set of imports using a list of directories, recursively
--   resolving imports of imported source files.
findimports
  :: (MonadIO m, MonadThrow m)
  => [FilePath]
  -- ^ Search path
  -> M.Map P.Import ()
  -- ^ Set of unresolved imports
  -> m (M.Map P.Import (), M.Map P.Import SrcTree)
  -- ^ Sets of unresolved (including nested) imports and imports resolved
  -- to source trees
findimports dirs s = loop (Proc { left = s, done = mempty }) where

  -- | Try to resolve a set of imports by iterating over a set of source 
  --   directories. Repeat with any new unresolved imports discovered during a 
  --   pass.
  loop
    :: (MonadIO m, MonadThrow m)
    => Process (M.Map P.Import (), M.Map P.Import SrcTree)
    -- ^ Process imports in this pass
    -> m (M.Map P.Import (), M.Map P.Import SrcTree)
    -- ^ Final sets of unresolved and resolved imports
  loop search = do
    -- Make a resolution pass over search path
    (unp, unres, res) <- findset dirs mempty (Proc { left = left search,
      done = mempty })
    -- Filter imports that have already been processed on search path
    let
      (oldunres, oldres) = done search
      unp' = M.difference (M.difference unp oldunres) oldres
      p = (oldunres <> unres, oldres <> res)
    if M.null unp' then
      -- No unprocessed imports to resolve
      return p
    else
      -- New pass over search path to try to resolve new set of imports
      loop (Proc { left = unp, done = p })
  
  -- | Loop over a list of directories to resolve a set of imports keeping
  --   track of any new unresolved imports that arise.
  findset
    :: (MonadIO m, MonadThrow m)
    => [FilePath]
    -- ^ Remaining search path
    -> M.Map P.Import ()
    -- ^ Imports to be resolved in next loop
    -> Process (M.Map P.Import SrcTree)
    -- ^ Imports processed in this loop
    -> m (M.Map P.Import (), M.Map P.Import (), M.Map P.Import SrcTree)
    -- ^ New unprocessed, unresolved and resolved imports after loop
  findset [] new search = return (new, left search, done search)
  findset (dir:dirs) new search = do 
    (unp, unres, res) <- resolveimports dir (left search)
    findset dirs (new <> unp) (Proc { left = unres, done = (done search <> res) })
    
    
-- | Attempt to resolve a set of imports to files of directory.
resolveimports
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> M.Map P.Import ()
  -> m (M.Map P.Import (), M.Map P.Import (), M.Map P.Import SrcTree)
resolveimports dir set = do
  tried <- M.traverseWithKey (\ i () -> resolve dir i) set
  let 
    -- Unresolved 'Left', resolved imports 'Right'.
    (unres, pairs) = M.mapEither ((maybe . Left) () Right) tried
    
    -- Combine unresolved nested imports of resolved imports.
    (unproc, res) = sequenceA pairs
    
  return (unproc, unres, res)
      
  
-- | Attempt to resolve an import in a directory.
--
--   For an import 'name' looks for a file 'name.my'.
resolve
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -- ^ Directory to search
  -> P.Import
  -- ^ Import name
  -> m (Maybe (M.Map P.Import (), SrcTree))
  -- ^ May return a pair of a set of nested unresolved imports and a import
  -- source tree if import can be resolved.
resolve dir (P.Use (P.I_ l)) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    Just <$> sourcefile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
