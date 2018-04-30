{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
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

module My.Syntax.Import
  ( sourcefile
  , findimports
  , Subst(..)
  )
where

import My.Types.Syntax.Class
import My.Types.Interpreter (KeySource(..))
import qualified My.Types.Classes
import My.Syntax.Parser (program, parse)
import My.Util (Collect(..), collect, Susp(..), Batch(..))
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Typeable (Typeable)
import Data.Bifunctor (first)
import Data.Bitraversable (bitraverse)
import Data.Semigroup (Semigroup(..))
import Control.Applicative (liftA2)
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Free (MonadFree(..))


-- | A co-routine that yields lists of unresolved labels 'a',
-- resumable with possible substitutions, and returns a fully resolved value.
--
-- Applicative instance will merge unresolved labels
data Subst r a b = Subst (Batch (Susp (M.Map r ()) (M.Map r (Subst r a a))) b)
  deriving Functor
 
instance Ord r => Applicative (Subst r a) where
  pure = Subst . pure
  
  Subst bf <*> Subst ba = Subst (bf <*> ba)

  
type Src r = Syn (Subst Import r) r


instance (Syntax (Member r), Semigroup (Rec r), Block r) => Program (Src r) where
  type Body (Src r) = Syn (Subst Import r) (Rec r)
  
  prog_ body = block_ <$> body
  progUse_ i body = (Syn . Subst . Batch) (Susp (M.singleton i ()) undefined)

  
    

-- | Parse a source file and find imports
sourcefile
  :: (MonadIO m, MonadThrow m, Program (Src r))
  => FilePath
  -> m (M.Map Import (), Subst Import r r)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse program file
  >>= \ (Syn p) -> case p of
    Subst (Run _) -> return (M.empty, p)
    Subst (Batch s) -> do 
      (unres, res) <- findimports [dir] (yield s)
      return (unres, Subst (resume s res))
  where
    dir = System.FilePath.dropExtension file
        
        
-- | Process some imports
data Process a = Proc
  { left :: M.Map Import ()
  , done :: a
  }
        
-- | Find files to import.
--
--   Try to resolve a set of imports using a list of directories, recursively
--   resolving imports of imported source files.
findimports
  :: (MonadIO m, MonadThrow m, Program (Src r))
  => [FilePath]
  -- ^ Search path
  -> M.Map Import ()
  -- ^ Set of imports to process
  -> m (M.Map Import (), M.Map Import (Subst Import r r))
  -- ^ Sets of imports (including nested) remaining unresolved and imports resolved
  -- to source trees
findimports dirs s = loop (Proc { left = s, done = mempty }) where

  -- | Try to resolve a set of imports by iterating over a set of source 
  --   directories. Repeat with any new unresolved imports discovered during a 
  --   pass.
  loop
    :: (MonadIO m, MonadThrow m, Program (Src r))
    => Process (M.Map Import (), M.Map Import (Subst Import r r))
    -- ^ Process imports in this pass
    -> m (M.Map Import (), M.Map Import (Subst Import r r))
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
    :: (MonadIO m, MonadThrow m, Program (Src r))
    => [FilePath]
    -- ^ Remaining search path
    -> M.Map Import ()
    -- ^ Imports to be resolved in next loop
    -> Process (M.Map Import (Subst Import r r))
    -- ^ Imports processed in this loop
    -> m (M.Map Import (), M.Map Import (), M.Map Import (Subst Import r r))
    -- ^ New unprocessed, unresolved and resolved imports after loop
  findset [] new search = return (new, left search, done search)
  findset (dir:dirs) new search = do 
    (unp, unres, res) <- resolveimports dir (left search)
    findset dirs (new <> unp) (Proc { left = unres, done = (done search <> res) })
    
    
-- | Attempt to resolve a set of imports to files of directory.
resolveimports
  :: (MonadIO m, MonadThrow m, Program (Src r))
  => FilePath
  -> M.Map Import ()
  -> m (M.Map Import (), M.Map Import (), M.Map Import (Subst Import r r))
resolveimports dir set = do
  tried <- M.traverseWithKey (\ i () -> resolve dir i) set
  let 
    -- Unresolved 'Left', resolved imports 'Right'.
    (unres, pairs) = M.mapEither (maybe (Left ()) Right) tried
    
    -- Combine unresolved nested imports of resolved imports.
    (unproc, res) = sequenceA pairs
    
  return (unproc, unres, res)
      
  
-- | Attempt to resolve an import in a directory.
--
--   For an import 'name' looks for a file 'name.my'.
resolve
  :: (MonadIO m, MonadThrow m, Program (Src r))
  => FilePath
  -- ^ Directory to search
  -> Import
  -- ^ Import name
  -> m (Maybe (M.Map Import (), Subst Import r r))
  -- ^ May return a pair of a set of nested unresolved imports and a import
  -- source tree if import can be resolved.
resolve dir (Use (I_ l)) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    Just <$> sourcefile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
