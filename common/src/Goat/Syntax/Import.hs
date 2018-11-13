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


newtype Mod m r a = Mod { runMod :: m ([r] -> a) }
  deriving Functor
  
instance Applicative m => Applicative (Mod m r) where
  pure a = Mod (pure (\ _ -> a))
  Mod mrf <*> Mod mra = Mod (liftA2 (\ rf ra r -> rf r (ra r)) mrf mra)

instance (Applicative m, Local a) => Local (Mod m r a) where
  local_ n = pure (local_ n)
  
instance (Applicative m, Self a) => Self (Mod m r a) where
  self_ n = pure (self_ n)
  
instance (Applicative m, Field a) => Field (Mod m a) where
  type Compound (Mod m r a) = Mod m r (Compound a)
  
  e #. k = fmap (#. k) e
  
instance (Applicative m, Block a) => Block (Mod m r a) where
  type Stmt (Mod m r a) = Mod m r (Stmt a)
  
  block_ stmts = fmap block_ (sequenceA stmts)
  
instance (Applicative m, Extend a) => Extend (Mod m r a) where
  type Ext (Mod m r a) = Mod m r (Ext a)
  
  (#) = liftA2 (#)

instance (Applicative m, Num a) => Num (Mod m r a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  signum = fmap signum
  negate = fmap negate
  
instance (Applicative m, Fractional a) => Fractional (Mod m r a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)
  
instance (Applicative m, IsString a) => IsString (Mod m r a) where
  fromString = pure . fromString

instance (Applicative m, Lit a) => Lit (Mod m r a) where
  unop_ op = fmap (unop_ op)
  binop_ op = liftA2 (binop_ op)

instance (Applicative m, Let a) => Let (Mod m r a) where
  type Lhs (Mod m r a) = Lhs a
  type Rhs (Mod m r a) = Mod m r (Rhs a)
  
  l #= r = (l #=) <$> r
  
instance MonadReader [Import] m => Extern (Mod m a a) where
  use_ i = Mod (asks (handleUse (Use i)) <&> maybe
    (tell [e] 
  
instance (Block r, s ~ Rec r) => Extern (Kr s r) where
  use_ i = block_ <$> Kr (gen (use_ i))

-- For an 'ExprDen (Member r)' let 'r ~ Rec (Member r)' be the block 'builder' type.
-- Then 'Global (Src r r)' is satisfied.
class
  ( -- implies 'Syntax (Src r (Member r))'
    Expr (Member r), r ~ Rec (Member r), Sep r
    -- with 'Member (Src r r) = Src r (Member r)' implies
    --    'Syntax (Member (Src r r)) => Global (Src r r)'
  ) => Deps r where
  prelude_ :: r -> r -> r

instance Deps r => Global (Kr r r) where
  type Body (Kr r r) = Kr r r
  type Prelude (Kr r r) = Import
  
  -- (#...) :: Import -> Src r r -> Src r r
  i #... xs = liftA2 prelude_ (Kr (gen i)) xs

  

-- | Parse a source file and find imports
sourcefile
  :: (MonadIO m, MonadThrow m, Deps r)
  => FilePath
  -> m (Src r r)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse program file
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
