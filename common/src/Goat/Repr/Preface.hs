{-# LANGUAGE DeriveFunctor, FlexibleContexts, FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving, LambdaCase, DeriveFunctor #-}

-- | Module containing logic for resolving import names to paths
module Goat.Repr.Preface
  ( module Goat.Repr.Preface
  , Identity
  )
where

import Goat.Lang.Parser (Parser, tokens, parse)
import Goat.Lang.Error (ImportError(..))
import Goat.Lang.Class
import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Bound (abstract, (>>>=), Scope)
import Bound.Scope (hoistScope)
import Control.Applicative (Const(..))
import Data.Bifunctor (Bifunctor(..))
import Data.Bifoldable (Bifoldable(..))
import Data.Bitraversable (Bitraversable(..))
import Data.Discrimination (Grouping, nub)
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
data Preface a b c = Preface (Imports a b) c
  deriving Functor
type Imports a = Assocs' ((,,) [a]) a

bindDefer
 :: ( Grouping k, Eq k
    , Foldable f, Functor f
    , Bifoldable p, Bifunctor p
    , Foldable (q k), Functor (q k)
    , Foldable m, Monad m
    )
 => a
 -> Bindings
      f (Defns p ((,,) [c]) q k) m (VarName k k a)
 -> Bindings
      f (Defns p ((,,) [c]) q k) m (VarName k k a)
bindDefer a bs = bs'
  where
  bs'
    = Match
        (Tag (Left (Tag (Right p))))
        (return (Right a))
        (hoistBindings lift bs
         >>>= abstractMatch ns . return)
  p = Matches
        (Assocs (map (\ n -> ([], n, pure ())) ns))
  ns
    = nub
        (foldMap
          (\case
          Left (Left (Local n)) -> [n]
          _ -> [])
          bs)

abstractMatch
 :: (Monad m, Eq a)
 => [a]
 -> m (VarName a b c)
 -> Scope (Local (Maybe Int)) m (VarName a b c)
abstractMatch ns
  = abstract
      (\case
      Left (Left (Local n))
       -> Local  . Just <$> elemIndex n ns
      
      _
       -> Nothing)

bindPreface
 :: (Eq a, Bifunctor p, Bifunctor q, Monad m)
 => Preface a
      (Bindings
        Identity
        (Defns p q (AnnCpts [a]) a)
        m
        (Import a))
      (Bindings
        Identity
        (Defns p q (AnnCpts [a]) a)
        m
        (Import a))
 -> Bindings
      Identity
      (Defns p q (AnnCpts [a]) a)
      m
      (Import a)
bindPreface (Preface im bcs) =
  Index (abstractImports ns bpcs)
  where
    bps = bindImports im
    bpcs
      = liftBindings2
          Parts (transBindings (Tag . Right) bps) bcs
          
    ns
      = getConst 
          (transverseBindings (Const . getNames) bps)
    
    getNames :: Assocs' ((,,) a) b c -> [b]
    getNames (Assocs ps) = [b | (_, b, _) <- ps]
    
    abstractImports
     :: (Functor f, Functor p, Monad m, Eq a)
     => [a]
     -> Bindings f p m (Import a)
     -> Bindings f p (Scope (Local Int) m) (Import a)
    abstractImports ns bs
      = hoistBindings lift bs
     >>>= abstract
            (\ (Import n)
             -> Local <$> elemIndex n ns)
            . return

bindImports
 :: (Functor p, Monad m)
 => Imports a (Bindings Identity p m b)
 -> Bindings (AnnCpts [a] a) p m b
bindImports (Assocs ps)
  = foldMap
      (\ (ns, n, Identity bs)
       -> embedBindings (bindName ns n) bs)
      ps
  where
  bindName
   :: Monad m
   => a -> b -> Identity c
   -> Bindings (AnnCpts a b) p m c
  bindName a b ic =
    Define (Assocs [(a, b, return <$> ic)])


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
