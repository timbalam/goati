{-# LANGUAGE TypeFamilies, RankNTypes #-}
module Goat.Repr.Pattern.Lang
  where

import Goat.Comp (run)
import Goat.Lang.Field
  ( Field_(..)
  , SomeVarChain, fromVarChain, SomePath, fromPath
  )
import Goat.Lang.Let
  ( Let_(..)
  , SomeMatch, fromMatch 
  )
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Repr.Pattern
  ( Paths(..), wrapPaths
  , Assoc, singleton
  , Declared, wrapDeclared, hoistDeclared
  , Local(..), Public(..)
  , Bindings(..), IdxBindings
  , Pattern(..)
  , crosswalkPattern
  , Multi(..)
  )
import Data.Align (Align(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.These (These(..), these, mergeTheseWith)
import Data.Semigroup ((<>))
import Data.Void (absurd)


-- | Binding 
data Relative a = Self | Parent a

instance IsString a => IsString (Relative a) where
  fromString "" = Self
  fromString s = Parent (fromString s)

instance Field_ a => Field_ (Relative a) where
    type Compound (Relative a) = Compound a
    m #. k = Parent (m #. k)
    
newtype ReadChain =
  ReadChain {
    readChain
     :: forall a . Paths Assoc a -> Declared Either Assoc a
    }

publicChain
 :: ReadChain -> ReadChain
publicChain (ReadChain f) =
  ReadChain (hoistDeclared toPub . f)
  where
    toPub
     :: Either (Public a) (Local a)
     -> Either (Public a) (Local a)
    toPub = Left . Public . either getPublic getLocal

instance IsString ReadChain where
  fromString s =
    ReadChain
      (wrapDeclared . singleton (fromString s) . Right . Local)

instance Field_ ReadChain where
  type
    Compound ReadChain = Relative ReadChain
  
  Self #. n =
    ReadChain (wrapDeclared . singleton n . Left . Public)
  Parent (ReadChain f) #. n =
    ReadChain (f . wrapPaths . singleton n)

readChainProof :: SomeVarChain -> Relative ReadChain
readChainProof = run . fromVarChain

newtype ReadPath =
  ReadPath {
    readPath
     :: forall a . a -> Declared These Assoc a
    }

setPath :: ReadChain -> ReadPath
setPath (ReadChain f) =
  ReadPath (hoistDeclared toThese . f . Leaf)
  where
    toThese
     :: Either (Public a) (Local a) 
     -> These (Public a) (Local a)
    toThese = either This That

instance IsString ReadPath where
  fromString s = setPath (fromString s)

instance Field_ ReadPath where
  type Compound ReadPath = Relative ReadChain
  p #. k = setPath (p #. k)


newtype ReadPattern =
  ReadPattern {
    readPattern
     :: forall a . a 
     -> IdxBindings
          (Declared These Assoc)
          (Pattern (Declared These Assoc))
          a
    }

setPattern :: ReadPath -> ReadPattern
setPattern (ReadPath f) = ReadPattern (In . f . pure)

dropPattern :: ReadPattern
dropPattern = ReadPattern (const mempty)

instance IsString ReadPattern where
  fromString s = setPattern (fromString s)
        
instance Field_ ReadPattern where
  type Compound ReadPattern = Relative ReadChain
  p #. n = setPattern (p #. n)

instance Block_ ReadPattern where
  type Stmt ReadPattern = ReadMatch
  block_ bdy = 
    ReadPattern
      (crosswalkPattern
        (foldMap readPattern)
        (Pattern (readDecomp (block_ bdy)) (pure dropPattern)))

instance Extend_ ReadPattern where
  type Ext ReadPattern = ReadDecomp
  p # ReadDecomp d =
    ReadPattern
      (crosswalkPattern (foldMap readPattern) (Pattern d (pure p)))

newtype ReadDecomp =
  ReadDecomp {
    readDecomp
     :: Declared These Assoc (NonEmpty ReadPattern)
    }

instance Block_ ReadDecomp where
  type Stmt ReadDecomp = ReadMatch
  block_ bdy =
    ReadDecomp
      (getMulti (foldMap (Multi . fmap pure . readMatch) bdy))


-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun
 :: Let_ s 
 => (a -> Lhs s)
 -> (b -> Rhs s)
 -> Pun a b -> s
pun f g (Pun a b) = f a #= g b

instance (IsString p, IsString a) => IsString (Pun p a) where
  fromString n = Pun (fromString n) (fromString n)

instance (Field_ p, Field_ a) => Field_ (Pun p a) where
  type Compound (Pun p a) = Pun (Compound p) (Compound a)
  Pun p a #. n = Pun (p #. n) (a #. n)


newtype ReadMatch =
  ReadMatch {
    readMatch :: Declared These Assoc ReadPattern
    }

punMatch = pun (setPath . publicChain) id
    
instance IsString ReadMatch where
  fromString s = punMatch (fromString s)

instance Field_ ReadMatch where
  type Compound ReadMatch =
    Pun (Relative ReadChain) (Relative ReadChain)
  p #. k = punMatch (p #. k)

instance Let_ ReadMatch where
  type Lhs ReadMatch = ReadPath
  type Rhs ReadMatch = ReadPattern
  ReadPath f #= a = ReadMatch (f a)

readMatchProof :: SomeMatch -> ReadMatch
readMatchProof = run . fromMatch
