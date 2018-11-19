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
import Data.List (nub, mapMaybe)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Typeable (Typeable)
import qualified Data.Map as M
import qualified Data.Set as S
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


data Mod f = Mod [Ident] (Repr f)

moduleError
 :: MonadWriter [StaticError k] m
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
      
type ResMod k = ReaderT [Ident] (Writer [StaticError k])
type ResInc k f = ReaderT [Mod f] (Writer [StaticError k])

runResMod :: ResMod k a -> [Ident] -> ([StaticError k], a)
runResMod r ns = (swap . runWriter) (runReaderT r ns)

runResInc :: ResInc k f a -> [Mod f] -> ([StaticError k], a)
runResInc r mods = (swap . runWriter) (runReaderT r mods)
    
includeMod
 :: Res k (Eval (Dyn k f))
 -- ^ Value being evaluated
 -> ResInc k (Dyn k f) (Mod (Dyn k f))
 -- ^ Included module
 -> ResMod k (ResInc (Dyn k f) (Repr (Dyn k f)))
includeMod res mod = reader (\ ns -> do
  Mod ks r <- mod
  mods <- ask
  let 
    rs = map (r #.) ks
    (ees, ev) =  runRes res ns [ks]
    r' = runEval ev mods [rs]
  tell ees
  return r')


dynCheckImports
  :: (MonadWriter [StaticError k] f)
  => Comps S.Ident [f (Maybe a)]
  -> f (M.Map S.Ident (Either [DefnError k] a))
dynCheckImports (Comps kv) = traverseMaybeWithKey
  check
  kv
  where 
    check
     :: (MonadWriter [StaticError k] f)
     => S.Ident -> [f a]
     -> f (Maybe (Either (StaticError k) a))
    check n fas = case fas of
      []       -> 
        tell [e] >>
          (return . Just) (Left e)
      (fa:[])  ->
        fmap (fmap Right) fa
      (fa:fas) ->
        tell [e] >> fa >> sequenceA fas >>
          (return . Just) (Left e)
      where
        e = DefnError (DuplicateImport n)


newtype Include k f =
  Include { getInclude :: ResMod k (ResInc k f (Mod f)) }

instance Include (Include k (Dyn k f)) where
  type Inc (Include k (Dyn k f)) = Module k (Dyn k f)
  include_ n (Module ks a) = Include
    (asks (handleUse n)
      >>= maybe
        (tell [e] >> return (pure (moduleError e)))
        (return . reader)
      >>= includeMod a
      >>= return . fmap (Mod ks) )
    where
      e = ImportError (NotModule n)

      
data Module k f = Module [Ident] (Res k (Eval f))

instance Module (Module k (Dyn k f)) where
  type ModuleStmt (Module k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = Module ks (block_ rs)
    where
      ks = nub
        (foldMap (\ (Stmt (ps, _)) -> mapMaybe pubname ps) rs)
        
      pubname :: P.Vis (Path k) (Path k) -> Maybe Ident
      pubname (P.Pub (Path n _)) = Just n
      pubname (P.Priv _)         = Nothing

      
data Import k f =
  Import
    (S.Set FilePath)
    (Src k f)
type Src k f =
  ReaderT
    (M.Map FilePath (ResMod k (ResInc k f (Mod f))))
    (ResMod k)
    (ResInc k f (Mod f))

instance Import (Import k f) where
  type ImportStmt =
    Stmt [Ident] (Plain Bind, FilePath)
  type Imp = Include Ident (DynIO Ident)
  extern_ rs (Include resmod) = Import 
    (S.fromList fps)
    (ReaderT (\ mods ->
      local (ns:)
        (liftA2 evalImport
          (dynCheckImports kv >>= resolveMods mods)
          resmod)))
    where
      
      resolveMods mods kv =
        M.traverse . either (return . moduleError) (mods!!)
    
      evalImport kv resinc = local (mods':) resinc
        where
          mods' = map (kv M.!) ns
      
      (kv, fps) = buildImports rs
      
      ns = nub
        (foldMap (\ (Stmt (ns, _)) -> ns) rs)
       
        
runFile
 :: FilePath
  -> IO ([StaticError k], Mod f)
runFile fp = 
  runStateT (sourceFile fp) M.empty
    >>= \ (resmod, kv) ->
      runResMod (do
        src <- resmod
        kv' <- sequenceA kv
        fixImports kv'
      
  where
    applyImports
      :: Reader (M.Map FilePath (Include k f))

fixImports
 :: M.Map FilePath (Src k f)
 -> ResInc k f (M.Map FilePath (Mod f))
fixImports kv = sequenceA kv'
  where
    kv' = fmap (\ r -> runReaderT r kv') kv
        
  

-- | Parse a source file and find imports
sourceFile
 :: FilePath
 -> StateT
      (M.Map FilePath (ResMod Ident (Src Ident (DynIO Ident))))
      IO
      (ResMod Ident (Src Ident (DynIO Ident)))
sourceFile file =
  liftIO (tryIOError (T.readFile file))
    >>= either
      (return . importerror)
      (resolveimport . parse program file)
  where
    resolveimport (Import fps resmod) = 
      traverse
        (liftIO
          . System.Directory.canonicalizePath
          . makeAbsolute cd)
        pfs
        >>= sourceDeps
        >> return resmod

    cd = dropFileName file
    makeAbsolute cd fp = case System.FilePath.isRelative fp of
      True -> System.FilePath.normalise (cd </> fp)
      False -> fp
      
    importerror :: IOError -> Src k (DynIO k)
    importerror err =
      tell [e] >> return (moduleError e)
      where
        e = ImportError err
      
    
-- | Update import cache with dependencies
sourceDeps
 :: [FilePath]
 -> StateT
      (M.Map FilePath (ResMod Ident (Src Ident (DynIO Ident))))
      IO
      ()
sourceDeps fps = do
  newfps <- gets (S.difference fps . M.keySet)
  newmods <- sequenceA (M.fromSet sourceFile newfps)
  modify (M.union newMods)
  