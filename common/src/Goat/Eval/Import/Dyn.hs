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

module Goat.Eval.Import.Dyn
  ( runFile, Mod(..), Include(..)
  , Import(..), evalImport, applyImports )
where

import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
import Goat.Syntax.Parser (program, parse)
import Goat.Syntax.Patterns
import Goat.Error
import Goat.Eval.Dyn
import Goat.Eval.IO.Dyn (DynIO, matchPlain)
import Goat.Util ((<&>), traverseMaybeWithKey, Compose(..))
import Data.List (nub)
import Data.Tuple (swap)
import Data.Maybe (mapMaybe)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Applicative (liftA2)
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import System.IO.Error (tryIOError)


data Mod f = Mod [S.Ident] (Repr f)

moduleError
 :: (Applicative f, MonadWriter [StaticError k] m)
 => StaticError k -> m (Mod (Dyn k f))
moduleError e =
  tell [e]
    >> (return
    . Mod []
    . Repr
    . Block
    . const
    . throwDyn)
      (StaticError e)
      
      
type ResMod k = ReaderT [S.Ident] (Writer [StaticError k])
type ResInc k f = ReaderT [Mod f] (Writer [StaticError k])

runResMod :: ResMod k a -> [S.Ident] -> ([StaticError k], a)
runResMod r ns = (swap . runWriter) (runReaderT r ns)

runResInc :: ResInc k f a -> [Mod f] -> ([StaticError k], a)
runResInc r mods = (swap . runWriter) (runReaderT r mods)


evalImport
 :: ResMod k (ResInc k f (Mod f))
 -> ([StaticError k], Repr f)
evalImport resmod = do
  resinc <- runResMod resmod []
  Mod _ e <- runResInc resinc []
  return e


includeMod
 :: (Applicative f, Foldable f, S.Self k, Ord k)
 => Res k (Eval (Dyn k f))
 -- ^ Value being evaluated
 -> ResInc k (Dyn k f) (Mod (Dyn k f))
 -- ^ Included module
 -> ResMod k (ResInc k (Dyn k f) (Repr (Dyn k f)))
includeMod res resinc = plainMod res <&>
  (\ f -> do
    Mod ks r <- resinc
    let
      rs = map (r S.#.) ks
      r0 :: Applicative f => Repr (Dyn k f)
      r0 = (Repr . Block . const . dyn) (DynMap Nothing Map.empty)
    f [ks] [(rs, r0)])


plainMod
 :: Res k (Eval f)
 -> ResMod k
      ([[S.Ident]]
        -> [([Repr f], Repr f)]
        -> ResInc k f (Repr f))
plainMod res = reader (\ ns nns scopes -> do 
  mods <- asks (map (\ (Mod _ r) -> r))
  let 
    (es, ev) = runRes res ns nns
    r' = runEval ev mods scopes
  tell es >> return r')


dynCheckImports
  :: (MonadWriter [StaticError k] f)
  => Comps S.Ident [Maybe a]
  -> f (Map S.Ident (Either (StaticError k) a))
dynCheckImports (Comps kv) = traverseMaybeWithKey
  check
  kv
  where 
    check
     :: (MonadWriter [StaticError k] f)
     => S.Ident -> [Maybe a]
     -> f (Maybe (Either (StaticError k) a))
    check n mbs = case mbs of
      []       -> 
        tell [e] >> (return . Just) (Left e)
      (mb:[])  ->
        return (Right <$> mb)
      (mb:mbs) ->
        tell [e] >> (return . Just) (Left e)
      where
        e = DefnError (DuplicateImport n)


newtype Include k f =
  Include { getInclude :: ResMod k (ResInc k f (Mod f)) }
  
includePlainModule :: Module k f -> Include k f
includePlainModule (Module ks res) =
  Include (plainMod res <&> (\ f -> f [] [] <&> Mod ks))
  
instance (Ord k, S.Self k, Applicative f, Foldable f)
 => S.Module (Include k (Dyn k f)) where
  type ModuleStmt (Include k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = includePlainModule (S.module_ rs)

instance (Applicative f, Foldable f, S.Self k, Ord k)
 => S.Include (Include k (Dyn k f)) where
  type Inc (Include k (Dyn k f)) = Module k (Dyn k f)
  include_ n (Module ks res) = Include
    (asks (handleUse n)
      >>= maybe
        (tell [e] >> return (moduleError e))
        (return . reader)
      >>= includeMod res
      >>= return . fmap (Mod ks) )
    where
      e = ScopeError (NotModule n)

      
data Module k f = Module [Ident] (Res k (Eval f))

instance (S.Self k, Ord k, Foldable f, Applicative f)
 => S.Module (Module k (Dyn k f)) where
  type ModuleStmt (Module k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = Module ks (readSynt (S.block_ rs))
    where
      ks = nub
        (foldMap (\ (Stmt (ps, _)) -> mapMaybe pubname ps) rs)
        
      pubname :: P.Vis (Path k) (Path k) -> Maybe S.Ident
      pubname (P.Pub (Path n _)) = Just n
      pubname (P.Priv _)         = Nothing

      
data Import k f =
  Import
    [FilePath]
    (ReaderT 
      [ResMod k (ResInc k f (Mod f))]
      (ResMod k)
      (ResInc k f (Mod f)))
    
importPlainInclude :: Include k f -> Import k f
importPlainInclude (Include resmod) =
  Import [] (lift resmod)

importPlainModule :: Module k f -> Import k f
importPlainModule = importPlainInclude . includePlainModule

instance (Applicative f, Foldable f, S.Self k, Ord k)
 => S.Module (Import k (Dyn k f)) where
  type ModuleStmt (Import k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = importPlainModule (S.module_ rs)
    
instance (Applicative f, Foldable f, S.Self k, Ord k)
 => S.Include (Import k (Dyn k f)) where
  type Inc (Import k (Dyn k f)) = Module k (Dyn k f)
  include_ n inc = importPlainInclude (S.include_ n inc)
  
  
applyImports
  :: [S.Ident]
  -> [ResMod k (ResInc k f (Mod f))]
  -> ResMod k (ResInc k f a)
  -> ResMod k (ResInc k f a)
applyImports ns resmods resmod = 
  local (ns++) (liftA2 evalImport' (sequenceA resmods) resmod)
    where
      evalImport' resincs resinc = do 
        mods <- ask
        let
          (es, mods') = runResInc (sequenceA resincs) (mods'++mods)
        tell es 
        (local (mods'++) resinc)


instance (Applicative f)
 => S.Imports (Import k (Dyn k f)) where
  type ImportStmt (Import k (Dyn k f)) =
    Stmt [S.Ident] (Plain Bind, FilePath)
  type Imp (Import k (Dyn k f)) = Include k (Dyn k f)
  extern_ rs (Include resmod) = Import 
    fps'
    (ReaderT (\ mods ->
      (dynCheckImports kv
        >>= \ kv ->
          applyImports
            ns
            (map (resolveMods mods kv Map.!) ns)
            resmod)))
    where
      resolveMods mods =
        Map.map
          (either
            (return . moduleError)
            (mods!!))
      
      (kv, fps) = buildImports rs
      
      fps' = foldMap (\ (p, a) -> matchPlain p a) fps
      
      ns = nub
        (foldMap (\ (Stmt (ns, _)) -> ns) rs)


type Src k f =
  ReaderT
    (Map FilePath (ResMod k (ResInc k f (Mod f))))
    (ResMod k)
    (ResInc k f (Mod f))


runFile
 :: (Applicative f, Foldable f, Ord k, S.Self k)
 => FilePath
 -> IO (ResMod k (ResInc k (Dyn k f) (Mod (Dyn k f))))
runFile file = runSource (sourceFile file)
    
runSource
 :: StateT (Map FilePath (Src k f)) IO (Src k f)
 -> IO (ResMod k (ResInc k f (Mod f)))
runSource m = 
  runStateT m Map.empty
    <&> (\ (src, kv) ->
      runReaderT src (fix (traverse runReaderT kv)))

-- | Parse a source file and find imports
sourceFile
 :: (Applicative f, Foldable f, Ord k, S.Self k)
 => FilePath
 -> StateT
      (Map FilePath (Src k (Dyn k f)))
      IO
      (Src k (Dyn k f))
sourceFile file =
  liftIO (importFile file) >>= resolveImport cd
  where
    cd = System.FilePath.dropFileName file

importFile 
 :: (Applicative f, Foldable f, Ord k, S.Self k)
 => FilePath
 -> IO (Import k (Dyn k f))
importFile file =
  tryIOError (T.readFile file)
    <&> either
          (throw . ImportError)
          (either
            (throw . ParseError)
            id
              . parse program file)
  where
    throw
      :: Applicative f
      => StaticError k -> Import k (Dyn k f)
    throw e =
      Import [] (tell [e] >> return (moduleError e))
      

resolveImport
 :: (Applicative f, Foldable f, Ord k, S.Self k)
 => FilePath
 -> Import k (Dyn k f)  
 -> StateT (Map FilePath (Src k (Dyn k f)))
      IO
      (Src k (Dyn k f))
resolveImport cd (Import files src) = 
  traverse
    (liftIO
      . System.Directory.canonicalizePath
      . System.FilePath.combine cd)
    files
    >>= sourceDeps . Set.fromList
    >> return (ReaderT (\ kv ->
      runReaderT src (map (kv Map.!) files)))


-- | Update import cache with dependencies
sourceDeps
 :: (Applicative f, Foldable f, Ord k, S.Self k)
 => Set FilePath
 -> StateT
      (Map FilePath (Src k (Dyn k f)))
      IO
      ()
sourceDeps files = do
  newfiles <- gets (Set.difference files . Map.keysSet)
  newmods <- sequenceA (Map.fromSet sourceFile newfiles)
  modify (Map.union newmods)
  