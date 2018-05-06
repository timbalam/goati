{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}
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
  , Src(..)
  )
where

import My.Types.Syntax.Class
import My.Types.Interpreter (KeySource(..))
import qualified My.Types.Classes
import My.Syntax.Parser (global, parse)
import My.Util (Collect(..), collect, Susp(..))
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

-- | A co-routine that yields sets of unresolved 'imports',
-- and resumes once when , imports are fully resolved, and
-- returns a fully resolved value.
--
-- Applicative instance will merge unresolved labels. Uses a phantom type
-- to avoid overlapping class instances.
newtype Src' t r a = Src { getSrc :: (M.Map Import (), M.Map Import r -> a) }
  deriving (Functor, Semigroup, Monoid)
  
data S -- ^ Phantom type indicating resumed value is resolved immediately
data D -- ^ Phantom type indicating resumed value is modified

type Gen = Src' S
type Src = Src' D

gen :: Import -> Gen r r
gen i = Src (M.singleton i (), (M.! i))
  
instance Applicative (Src' t r) where
  pure = Src . pure . pure
  
  Src pf <*> Src pa = Src (liftA2 (<*>) pf pa)
    
instance Local a => Local (Src' t r a) where
  local_ = pure . local_ 
  
instance Self a => Self (Src' t r a) where
  self_ = pure . self_
  
instance Field a => Field (Src' t r a) where
  type Compound (Src' t r a) = Src' t r (Compound a)
  
  e #. k = fmap (#. k) e
  
instance Path a => Path (Src' t r a)
instance RelPath a => RelPath (Src' t r a)
instance VarPath a => VarPath (Src' t r a)

type instance Member (Src' t  r a) = Src' t r (Member a)
  
instance Tuple a => Tuple (Src' t r a) where
  type Tup (Src' t r a) = Src' t r (Tup a)
  
  tup_ = fmap tup_
  
instance (Block a) => Block (Src' t r a) where
  type Rec (Src' t r a) = Src' t r (Rec a)
  
  block_ = fmap block_
  
instance Extend a => Extend (Src' t r a) where
  type Ext (Src' t r a) = Src' t r (Ext a)
  
  (#) = liftA2 (#)
  
instance Defns a => Defns (Src' t r a)

instance Lit a => Lit (Src' t r a) where
  int_ = pure . int_
  num_ = pure . num_
  str_ = pure . str_
  
  unop_ op = fmap (unop_ op)
  binop_ op = liftA2 (binop_ op)
  
instance Expr a => Expr (Src' t r a)

instance Let a => Let (Src' t r a) where
  type Lhs (Src' t r a) = Lhs a
  type Rhs (Src' t r a) = Src' t r (Rhs a)
  
  l #= r = (l #=) <$> r

instance TupStmt a => TupStmt (Src' t r a)
instance RecStmt a => RecStmt (Src' t r a)
  
instance Extern (Gen r r) where
  use_ i = gen i
  
instance (Block r, s ~ Rec r) => Extern (Src s r) where
  use_ i = block_ <$> Src s
    where 
      Src s = use_ i :: Gen r r
    
instance Expr r => Syntax (Gen r r)

instance (Expr r, s ~ Rec r) => Syntax (Src' D s r)

-- For an
--    Expr (Member r)
-- let 
--    r ~ Rec (Member r)
-- be the block 'builder' type.
-- Then
--     'Global (Src r r)'
class
  ( -- implies 'Syntax (Src' D r (Member r))'
    Expr (Member r), r ~ Rec (Member r), Semigroup r
    -- with 'Member (Src' t r r) = Src' t r (Member r)' implies
    --    'Syntax (Member (Src' D r r)) => Global (Src' D r r)'
  ) => Deps r

instance Deps r => Global (Src r r) where
  type Body (Src r r) = Src r r
  
  -- (#...) :: Import -> Src r r -> Src r r
  i #... xs = xs


-- | Parse a source file and find imports
sourcefile
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -> m (Src r r)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse global file
  >>= sourcedeps
  where
    sourcedeps :: (MonadIO m, MonadThrow m, Deps r) => Src r r -> m (Src r r)
    sourcedeps (Src (y, k)) = do
      (unres, res) <- findimports [dir] y
      (return . Src) (unres, k . substres res)
  
    dir = System.FilePath.dropExtension file
    
    substres :: M.Map Import (M.Map Import r -> r) -> M.Map Import r -> M.Map Import r
    substres res m = m' 
      where
        m' = M.map ($ M.union m' m) res
        
        
        
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
  :: (MonadIO m, MonadThrow m, Deps r)
  => [FilePath]
  -- ^ Search path
  -> M.Map Import ()
  -- ^ Set of imports to process
  -> m (M.Map Import (), M.Map Import (M.Map Import r -> r))
  -- ^ Sets of imports resolved to source files
findimports dirs y = loop (Proc { left = y, done = mempty }) where

  -- | Try to resolve a set of imports by iterating over a set of source 
  --   directories. Repeat with any new unresolved imports discovered during a 
  --   pass.
  loop
    :: (MonadIO m, MonadThrow m, Deps r)
    => Process (M.Map Import (), M.Map Import (M.Map Import r -> r))
    -- ^ Process imports in this pass
    -> m (M.Map Import (), M.Map Import (M.Map Import r -> r))
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
    -> M.Map Import ()
    -- ^ Imports to be resolved
    -> m (M.Map Import (), M.Map Import (Src r r))
    -- ^ Resolved imports after loop
  findset dirs y = loop dirs (Proc { left = y, done = mempty }) where
    loop
      :: (MonadIO m , MonadThrow m, Deps r)
      => [FilePath]
      -> Process (M.Map Import (Src r r))
      -> m (M.Map Import (), M.Map Import (Src r r))
    loop [] search = return (left search, done search)
    loop (dir:dirs) search = do 
      (unres, res) <- resolveimports dir (left search)
      loop dirs (Proc { left = unres, done = (done search <> res) })
    
    
-- | Attempt to resolve a set of imports to files of directory.
resolveimports
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -> M.Map Import ()
  -> m (M.Map Import (), M.Map Import (Src r r))
resolveimports dir set = do
  tried <- M.traverseWithKey (\ i () -> resolve dir i) set
   -- Unresolved 'Left', resolved imports 'Right'.
  return (M.mapEither (maybe (Left ()) Right) tried)
      
  
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
