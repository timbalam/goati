{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, LambdaCase, DeriveFunctor #-}

-- | Module containing logic for resolving import names to paths
module Goat.Repr.Preface where

import Goat.Lang.Parser (Parser, tokens, parse)
import Goat.Lang.Error (ImportError(..))
import Goat.Lang.Class
import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Bound (abstract, (>>>=), Scope)
import Bound.Scope (hoistScope)
import Control.Applicative (Const(..))
import Data.Bifoldable (bifoldMap)
import Data.Bitraversable (bitraverse)
import Data.Functor (($>))
import Data.Functor.Identity (Identity(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
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
import Text.Parsec (ParseError)
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
data Preface f a b = Preface (AmbigImports f a) b
  deriving Functor
type AmbigImports f
  = Inside (Ambig f) (Map Ident)
type Module f m
  = Bindings (Cpts f) (Cpts f)
      (Scope (Super Ident) (Scope (Public Ident) m))

bindDefer
 :: (Foldable f, Applicative f, Foldable m, Monad m)
 => a
 -> Module f m (VarName b Ident a)
 -> Module f m (VarName b Ident a)
bindDefer a bs = bs'
  where
  bs'
    = Match p
        (return (Right (Right a)))
        (hoistBindings lift bs
         >>>= hoistScope (lift . lift)
          . abstractLocal ns
          . return)
  
  (ns, p)
    = bitraverse
        (\ n -> ([Just n], pure ()))
        (\ () -> ([Nothing], ()))
        (Extend
          (Map.fromSet id (foldMap localSet bs))
          ())
   <&> \ (Extend kv ()) -> Inside kv
  
  localSet :: VarName a Ident b -> Set Ident
  localSet
    = \case 
      Right (Left (Local n)) -> Set.singleton n
      _ -> mempty

bindPreface
 :: MonadBlock (BlockCpts f) m
 => Preface ((,) w)
      (Bindings
        Identity (Cpts ((,) w)) m (Import Ident))
      (Bindings
        Identity (Cpts ((,) w)) m (Import Ident))
 -> Bindings Identity (Cpts ((,) w)) m (Import Ident)
bindPreface (Preface im bcs) =
  Index (abstractImports ns bpcs)
  where
    bps = bindImports im
    bpcs
      = liftBindings2 Parts bps bcs
          
    ns
      = getConst 
          (transverseBindings (Const . getNames) bps)
    
    getNames :: Cpts f a -> [Maybe Ident]
    getNames (Inside kv)
      = bifoldMap
          (\ n -> [Just n])
          (\ () -> [Nothing])
          (Extend (Map.mapWithKey const kv) ())
    
    abstractImports
     :: (Functor f, Functor p, Monad m, Eq a)
     => [Maybe a]
     -> Bindings f p m (Import a)
     -> Bindings f p (Scope (Local Int) m) (Import a)
    abstractImports ns bs =
      hoistBindings lift bs >>>=
        abstract
          (\ (Import n) ->
            Local <$> elemIndex (Just n) ns) .
          return

bindImports
 :: (Functor p, Monad m)
 => AmbigImports ((,) w) (Bindings Identity p m a)
 -> Bindings (Cpts ((,) w)) p m a
bindImports (Inside kv) =
  Map.foldMapWithKey
    (\ n (Ambig fs) ->
      foldMap
        (\ (w, bs)
         -> embedBindings (bindName w n) bs) fs)
    kv
  where
    bindName
     :: Monad m
     => w
     -> Ident
     -> Identity a
     -> Bindings (Cpts ((,) w)) p m a
    bindName w n (Identity a) =
      Define
        (Inside
          (Map.singleton n
            (Ambig (pure (w, return a)))))


-- | Parse a source file and find imports

type Source a b =
  StateT (Map FilePath (Either ImportError a)) IO b

runSource
 :: Source a b
 -> IO (b, Map FilePath (Either ImportError a))
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
 :: Traversable t
 => (FilePath -> Source a (Either ImportError a))
 -> FilePath
 -> t FilePath
 -> Source a (t FilePath)
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
