{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, LambdaCase, DeriveFunctor #-}

-- | Module containing logic for resolving import names to paths
module Goat.Repr.Preface where

import Goat.Lang.Parser (Parser, tokens)
import Goat.Lang.Class
import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Bound (abstract, Scope)
import Data.Bitraverse (bisequenceA)
import Data.Functor (($>))
import Data.List (elemIndex)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text.IO as Text
import Data.Text (Text)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import Text.Parsec (parse, ParseError)
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

-- data Defer a b = Defer (Maybe a) b deriving Functor
data Preface a b = Preface (Imports a) b deriving Functor
type Imports = Multi (Map Ident)

bindDefer
 :: (Monad m, Foldable m)
 => a
 -> Abs Components m (VarName b Ident a)
 -> Abs Components m (VarName b Ident a)
bindDefer a (Abs bs) = Abs bs'
  where
    bs' =
      letBind
        (Match p (Right (Right a)))
        (hoistBindings lift bs >>>= abstractLocal ns . return)
    
    (ns, p) =
      Components <$> 
        bisequenceA
          (Extend
            (Map.fromSet
              (\ n -> ([Just n], pure ()))
              (foldMap localSet bs))
            ([Nothing], ()))
    
    localSet :: VarName a Ident b -> Set Ident
    localSet (Right (Left (Local n))) = Set.singleton n
    localSet _ = mempty

bindPreface
 :: MonadBlock (Abs Components) m
 => Preface 
      (Block Components m (Maybe (Import Ident)))
      (Block Components m (Maybe (Import Ident)))
 -> Block Components m (Maybe (Import Ident))
bindPreface (Preface m bcs) = Let (abstractImports ns bpcs)
  where
    (p, bps) =
      squashBindings <$>
        transverseBindings importedComponents (bindImports m)
    ns = getNames p
    bpcs = liftBindings2 Parts bps bcs
    
    importedComponents
      :: MonadBlock (Abs Components) m
      => Imports a
      -> (Components (), Bindings Decompose p m a)
    importedComponents (Inside kv) =
      (p, Define (Match p m))
      where
        m = wrapBlock (Abs (Define (return <$> Inside x)))
        p = Components (x $> [])
        x = Extend kv ()
    
    getNames :: Components a -> [Maybe Ident]
    getNames (Components (Extend kv _)) =
      foldMap id
        (Extend
          (Map.mapWithKey (\ n _ -> [Just n]) kv)
          [Nothing])
    
    abstractImports
     :: (Functor f, Functor p, Monad m, Eq a)
     => [Maybe a]
     -> Bindings f p m (Import a)
     -> Bindings f p (Scope (Local Int) m) (Import a)
    abstractImports ns bs =
      hoistBindings lift bs >>>=
        abstract
          (\ (Import n) -> Local <$> elemIndex (Just n) ns)
          return

bindImports
 :: (Functor r, Functor p, MonadBlock (Abs r) m)
 => Imports (Bindings r p m a)
 -> Bindings Imports p m a
bindImports (Inside kv) =
  Map.foldMapWithKey
    (\ k vs -> foldMap (embedBindings (toWrappedField k)) vs)
    kv
  where
    toWrappedField
     :: (Functor r, MonadBlock (Abs r) m)
     => Ident -> r a -> Bindings Imports p m a
    toWrappedField k r =
      Define 
        (Inside
          (Map.singleton k
              [wrapBlock (Abs (Define (return <$> r)))]))


-- | Parse a source file and find imports

type Source a b =
  StateT (Map FilePath (Either ImportError a)) IO b

runSource
 :: Source a b -> IO (b, Map FilePath (Either ImportError a))
runSource m = runStateT m Map.empty

sourceFile
 :: MonadIO m 
 => Parser (FilePath -> m a)
 -> FilePath -> m (Either ImportError a)
sourceFile p file =
  liftIO (tryIOError (Text.readFile file))
   >>= \case
    Left e -> return (Left (IOError e))
    Right s ->
      case parse tokens file s >>= parse p file of
        Left e -> return (Left (ParseError e))
        Right f -> Right <$> f cd
  where
    cd = System.FilePath.dropFileName file


resolveImports
 :: (FilePath -> Source a (Either ImportError a))
 -> FilePath -> Imports FilePath -> Source a (Imports FilePath)
resolveImports src cd files = 
  do
    files' <- 
      traverse
        (liftIO
          . System.Directory.canonicalizePath
          . System.FilePath.combine cd)
        files
    sourceNewDeps src (foldMap Set.singleton files')
    return files'


-- | Update import cache with dependencies
sourceNewDeps
 :: (FilePath -> Source a (Either ImportError a))
 -> Set FilePath -> Source a ()
sourceNewDeps src files = do
  newfiles <- gets (Set.difference files . Map.keysSet)
  newdeps <- sequenceA (Map.fromSet src newfiles)
  modify (Map.union newdeps)

-- Missing import or parse error

data ImportError =
    ParseError ParseError
  | IOError IOError

displayImportError :: ImportError -> String
displayImportError (ParseError e) = show e
displayImportError (IOError e) = show e
