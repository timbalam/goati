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
--   A list of entry points can be provided via 'sourcedeps' allowing library 
--   code to be imported.

module My.Syntax.Import
  ( sourcefile
  , sourcedeps
  , checkimports
  , Src(..)
  , Kr(..)
  , Deps(..)
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
import GHC.Exts (IsList(..))
import Control.Applicative (liftA2)
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Free (MonadFree(..))

-- | A co-routine that yields sets of unresolved 'imports',
-- and resumes once when , imports are fully resolved, and
-- returns a fully resolved value.
--
-- Applicative instance will merge unresolved labels
newtype Src r a = Src { getSrc :: (M.Map Import KeySource, M.Map Import r -> a) }
  deriving Functor
  
newtype Kr r a = Kr { runKr :: KeySource -> Src r a }
  deriving Functor

gen :: Import -> KeySource -> Src r r
gen i f = Src (M.singleton i f, (M.! i))
  
instance Applicative (Src r) where
  pure = Src . pure . pure
  Src pf <*> Src pa = Src (liftA2 (<*>) pf pa)
  
instance Applicative (Kr r) where
  pure = Kr . pure . pure
  Kr rf <*> Kr ra = Kr (liftA2 (<*>) rf ra)
    
instance Local a => Local (Kr r a) where
  local_ = pure . local_ 
  
instance Self a => Self (Kr r a) where
  self_ = pure . self_
  
instance Field a => Field (Kr r a) where
  type Compound (Kr r a) = Kr r (Compound a)
  
  e #. k = fmap (#. k) e
  
instance Path a => Path (Kr r a)
instance RelPath a => RelPath (Kr r a)
instance VarPath a => VarPath (Kr r a)

type instance Member (Kr  r a) = Kr r (Member a)
  
instance Tuple a => Tuple (Kr r a) where
  type Tup (Kr r a) = Kr r (Tup a)
  
  tup_ = fmap tup_
  
instance Block a => Block (Kr r a) where
  type Rec (Kr r a) = Kr r (Rec a)
  
  block_ = fmap block_
  
instance Extend a => Extend (Kr r a) where
  type Ext (Kr r a) = Kr r (Ext a)
  
  (#) = liftA2 (#)
  
instance Defns a => Defns (Kr r a)

instance Lit a => Lit (Kr r a) where
  int_ = pure . int_
  num_ = pure . num_
  str_ = pure . str_
  
  unop_ op = fmap (unop_ op)
  binop_ op = liftA2 (binop_ op)
  
instance Expr a => Expr (Kr r a)

instance Let a => Let (Kr r a) where
  type Lhs (Kr r a) = Lhs a
  type Rhs (Kr r a) = Kr r (Rhs a)
  
  l #= r = (l #=) <$> r

instance TupStmt a => TupStmt (Kr r a)
instance RecStmt a => RecStmt (Kr r a)

instance Sep a => Sep (Kr r a) where
  (#:) = liftA2 (#:)
  
instance Splus a => Splus (Kr r a) where
  empty_ = pure empty_
  
instance (Block r, s ~ Rec r) => Extern (Kr s r) where
  use_ i = block_ <$> Kr (gen i)
    
--instance Expr r => Syntax (Gen r r)

instance (Expr r, s ~ Rec r) => Syntax (Kr s r)

-- For an
--    Expr (Member r)
-- let 
--    r ~ Rec (Member r)
-- be the block 'builder' type.
-- Then
--     'Global (Src r r)'
class
  ( -- implies 'Syntax (Src r (Member r))'
    Expr (Member r), r ~ Rec (Member r), Sep r
    -- with 'Member (Src r r) = Src r (Member r)' implies
    --    'Syntax (Member (Src r r)) => Global (Src r r)'
  ) => Deps r where
  prelude_ :: r -> r -> r

instance Deps r => Global (Kr r r) where
  type Body (Kr r r) = Kr r r
  
  -- (#...) :: Import -> Src r r -> Src r r
  i #... xs = liftA2 prelude_ (Kr (gen i)) xs

  
-- | Error when an import name cannot be resolved to a source file.
data ImportError = ImportNotFound KeySource Import
  deriving (Eq, Show, Typeable)
  
instance My.Types.Classes.MyError ImportError where
  displayError (ImportNotFound src i) =
    "Not found: Module " ++ show i ++ "\nIn :" ++ show src
  

-- | Parse a source file and find imports
sourcefile
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -> m (Src r r)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse global file
  >>= sourcedeps [dir] . ($ (File file)) . runKr
  where
    dir = System.FilePath.dropExtension file
    

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
