{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}

-- | Module containing logic for resolving import names to paths
module Goat.Repr.Preface where

--import Goat.Comp (run)
import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
import Goat.Syntax.Parser (program, parse)
import Goat.Syntax.Patterns
import Goat.Lang.Extern (Extern(..))
--import Goat.Lang.Let (SomeDefn, fromDefn)
--import Goat.Lang.Preface
--  ( SomePreface, SomeLetImport, fromPreface, fromLetImport )
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
import Data.Void (Void)
import Control.Applicative (liftA2)
import Control.Monad.IO.Class
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import System.IO.Error (tryIOError)


{-
Preface
-------

Goat allows code to be imported using *use*s.
E.g. An import '@use modname' resolves to the code for module 
'modname'.

Module names are associated with source files in *extern* section of a *preface*,
via *import statements*.
E.g. the import statement 'modname = ../path/to/file.gt' assoicates the module name 'modname' with the corresponding source file.

Modules names unassociated in an imported file will be associated to the same names of the importing file.

The Goat interpreter will in the last case try to resolve any unassociated uses in the entry file
(for instance using a configuration file of installed packages),
and error on unassociated names.
-}

data Include b a = Program a | Include b a
data Preface a b = Preface (Imports a) b
type Imports a = Many (Map Ident) a
type Including = Inside (Include (Import Ident))
type Module f m a = Bindings (Abs f) (Match (Imports ())) m a

componentsReprFromAbs
 :: MonadBlock (Abs Components) m
 => Abs Components a -> (Components (), m a)
componentsReprFromAbs (Abs bs) = (p, a)
  where
    Const p = transverseBindings (Const . getComponents) bs
    a = wrapBlock (Abs (return <$> bs))
    
    getComponents :: Components a -> Components ()
    getComponents (Inside x) = Inside (x $> [()])

includeAbs
 :: MonadBlock (Abs Components) m
 => Abs Components (m (VarName a Ident b))
 -> Abs Components (m (VarName a Ident b))
 -> Abs Components (m (VarName a Ident b))
includeAbs (Abs bas) (Abs bbs) = Abs bbs'
  where
    bbs' =
      letBind
        (Match p (wrapBlock (Abs bas)))
        (bbs >>>= abstractLocal ns . return)
    
    Const p = transverseBindings (Const . getComponents) bas
    ns = getNames p
    
    getNames :: Components a -> [Just Ident]
    getNames (Many (Extend r _)) =
      foldMap
        (Extend (Map.mapWithKey (\ n _ -> [Just n])) [Nothing])

bindModules
 :: Monad m
 => Imports
      (Include (Import Ident)
        (Module f m (VarName a b (Import Ident))))
 -> Include (Import Ident)
      (Module f m (VarName a b (Import Ident)))
 -> Include (Import Ident)
      (Module f m (VarName a b (Import Ident)))
bindModules kv bs =
    letBind
      (kv <&> abstractImports ns . includeAbs )
      (abstractImports ns bs)
  where
    kv' = 
    ns = getImportNames kv
    
    getImportNames :: Imports a -> [Ident]
    getImportNames (Inside kv) =
      Map.foldMapWithKey (\ n _ -> [n]) kv
    
    abstractImports
     :: [Ident]
     -> Bindings f m (VarName a b (Import Ident))
     -> Bindings f (Scope (Local Int) m)
          (VarName a b (Import Ident))
    abstractImports ns =
      hoistBindings lift bs >>>=
        abstract (\case
          Left _ -> Nothing
          Right (Left _) -> Nothing
          Right (Right (Import n)) -> elemIndex ns n)

bindModulesFromImports
 :: ( MonadBlock (Abs (Including Components)) m
    , MonadBlock (Abs Components) n
    )
 => Imports (Include (Import Ident) (Module Components m a))
 -> Module Components m (n a)
bindModulesFromImports (Inside kv) =
  
  
  where
    kv' =
      Map.mapWithKey
        (\ k is ->
          map (\case
            Program mod -> Program <$> componentsRepr k mod
            Include b mod -> Include b <$> componentsRepr k mod)
            is)
        kv
  
    componentsRepr k m = (m', p)
      where
        (p, m') =
          transverseBindings
            (fmap (Map.singleton k))
            (embedBindings componentsReprFromAbs m)

-- | Parse a source file and find imports
sourceFile
 :: (FilePath -> IO (Imports FilePath a))
 -> FilePath
 -> StateT
      (Map FilePath (Imports FilePath a))
      IO
      (Imports FilePath a)
sourceFile imprt file =
  liftIO (imprt file) >>=
    resolveImport (sourceFile imprt) cd
  where
    cd = System.FilePath.dropFileName file

resolveImport
 :: (FilePath -> StateT (Map FilePath (Imports FilePath a)) IO ())
 -> FilePath
 -> Imports FilePath a
 -> StateT (Map FilePath (Imports FilePath a)) IO ()
resolveImport sourceOne cd (Imports (Import fs) mod) = 
  traverse
    (liftIO
      . System.Directory.canonicalizePath
      . System.FilePath.combine cd)
    files
    >>= sourceDeps sourceOne . Set.fromList


-- | Update import cache with dependencies
sourceDeps
 :: (FilePath -> StateT (Map FilePath (Imports FilePath a)) IO ())
 -> Set FilePath
 -> StateT (Map FilePath (Imports FilePath a)) IO ()
sourceDeps sourceOne files = do
  newfiles <- gets (Set.difference files . Map.keysSet)
  newmods <- sequenceA (Map.fromSet sourceOne newfiles)
  modify (Map.union newmods)



{-
data Import k f =
  Import
    [FilePath]
    (ReaderT 
      [ResMod k (ResInc k f (Mod f))]
      (ResMod k)
      (ResInc k f (Mod f)))
      
-- | Imported unresolved module with public fields.
data Module k f = Module [P.Ident] (Res k (Eval f))

-- | Imported and resolved module
data Mod f = Mod [P.Ident] (Repr f)

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
      
      
type ResMod k = ReaderT [P.Ident] (Writer [StaticError k])
type ResInc k f = ReaderT [Mod f] (Writer [StaticError k])


newtype Include k f =
  Include { getInclude :: ResMod k (ResInc k f (Mod f)) }
  

runResMod :: ResMod k a -> [P.Ident] -> ([StaticError k], a)
runResMod r ns = (swap . runWriter) (runReaderT r ns)

runResInc :: ResInc k f a -> [Mod f] -> ([StaticError k], a)
runResInc r mods = (swap . runWriter) (runReaderT r mods)

    
importPlainInclude :: Include k f -> Import k f
importPlainInclude (Include resmod) =
  Import [] (lift resmod)

importPlainModule :: Module k f -> Import k f
importPlainModule = importPlainInclude . includePlainModule

instance (Applicative f, Foldable f, S.IsString k, Ord k)
 => S.Module_ (Import k (Dyn k f)) where
  type ModuleStmt (Import k (Dyn k f)) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
  module_ rs = importPlainModule (S.module_ rs)

instance (Applicative f, Foldable f, S.IsString k, Ord k)
 => S.Include_ (Import k (Dyn k f)) where
  type Inc (Import k (Dyn k f)) = Module k (Dyn k f)
  include_ n inc = importPlainInclude (S.include_ n inc)
  
newtype ImportPath = ImportPath FilePath

instance S.Text_ ImportPath where
  quote_ = ImportPath
        
instance (Applicative f)
 => S.Imports_ (Import k (Dyn k f)) where
  type ImportStmt (Import k (Dyn k f)) =
    Stmt [P.Ident] (Plain Bind, ImportPath)
  type Imp (Import k (Dyn k f)) = Include k (Dyn k f)
  extern_ rs (Include resmod) = Import 
    fps'
    (ReaderT (\ mods ->
      (dynCheckImports kv'
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
      
      (Comps kv, fps) = buildImports rs
        :: ( Comps P.Ident [Maybe Int]
           , [(Plain Bind, ImportPath)]
           )
      
      kv' = Comps kv
      
      fps' = foldMap (\ (p, ImportPath fp) -> matchPlain p fp) fps
      
      ns = nub
        (foldMap (\ (Stmt (ns, _)) -> ns) rs)


evalImport
 :: ResMod k (ResInc k f (Mod f))
 -> ([StaticError k], Repr f)
evalImport resmod = do
  resinc <- runResMod resmod []
  Mod _ e <- runResInc resinc []
  return e


includeMod
 :: (Applicative f, Foldable f, S.IsString k, Ord k)
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
      ([[P.Ident]]
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
  => Comps P.Ident [Maybe a]
  -> f (Map P.Ident (Either (StaticError k) a))
dynCheckImports (Comps kv) = traverseMaybeWithKey
  check
  kv
  where 
    check
     :: (MonadWriter [StaticError k] f)
     => P.Ident -> [Maybe a]
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


  
applyImports
  :: [P.Ident]
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

type Src k f =
  ReaderT
    (Map FilePath (ResMod k (ResInc k f (Mod f))))
    (ResMod k)
    (ResInc k f (Mod f))


runFile
 :: (Applicative f, Foldable f, Ord k, S.IsString k)
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
 :: (Applicative f, Foldable f, Ord k, S.IsString k)
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
 :: (Applicative f, Foldable f, Ord k, S.IsString k)
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
 :: (Applicative f, Foldable f, Ord k, S.IsString k)
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
 :: (Applicative f, Foldable f, Ord k, S.IsString k)
 => Set FilePath
 -> StateT
      (Map FilePath (Src k (Dyn k f)))
      IO
      ()
sourceDeps files = do
  newfiles <- gets (Set.difference files . Map.keysSet)
  newmods <- sequenceA (Map.fromSet sourceFile newfiles)
  modify (Map.union newmods)
-}
