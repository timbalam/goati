{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts #-}
module Goat.Repr.Pattern.Lang
  where

import Goat.Comp (Comp)
import Goat.Lang.Reflect (handleAll)
import Goat.Lang.Field (Field_(..))
import Goat.Lang.Match (SomeVarField, fromVarFieldM)
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Repr.Assoc (Assoc, singleton)
import Goat.Repr.Pattern
  ( Paths(..), wrapPaths
  , Declared, wrapDeclared
  , Local(..), Public(..), Privacy
  , Stores(..), Many, Multi
  , Views(..)
  , Bindings(..), Matchings
  , Extend(..), Pattern
  , patternDeclared
  , MonadBlock, Abs
  )
import Data.Align (Align(..))
import Data.Bifunctor (first)
import Data.Biapplicative (bipure)
import Data.List.NonEmpty (NonEmpty(..))
import Data.These (These(..), these, mergeTheseWith)
import Data.Semigroup ((<>), Option)
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
     :: forall a .
          Paths Assoc a ->
          Declared Assoc (Privacy Either) a
    }

instance IsString ReadChain where
  fromString s =
    ReadChain
      (wrapDeclared .
        singleton (fromString s) .
        bipure (Right (Local ())))

instance Field_ ReadChain where
  type
    Compound ReadChain = Relative ReadChain
  
  Self #. n =
    ReadChain
      (wrapDeclared .
        singleton n .
        bipure (Left (Public ())))
  Parent (ReadChain f) #. n =
    ReadChain (f . wrapPaths . singleton n)

-- | Proof of instance 'VarField_ (Relative ReadChain)' with 'Compound (Relative ReadChain) ~ Relative ReadChain
readChainProof
 :: SomeVarField (Relative ReadChain) -> Relative ReadChain
readChainProof = handleAll fromVarFieldM

newtype ReadPath =
  ReadPath {
    readPath
     :: forall a . a ->
          Declared Assoc (Privacy These) a
    }

setPath :: ReadChain -> ReadPath
setPath (ReadChain f) =
  ReadPath (first toThese . f . Leaf)
  where
    toThese = either This That

instance IsString ReadPath where
  fromString s = setPath (fromString s)

instance Field_ ReadPath where
  type Compound ReadPath = Relative ReadChain
  p #. k = setPath (p #. k)


newtype ReadPattern =
  ReadPattern {
    readPattern
     :: forall m a .
          MonadBlock (Abs (Pattern (Option (Privacy These)))) m 
     => m a
     -> Bindings
          (Multi (Declared Assoc (Privacy These)))
          (Pattern (Option (Privacy These)) ())
          m
          a
    }

setPattern :: ReadPath -> ReadPattern
setPattern (ReadPath f) = ReadPattern (Define . Stores . f . pure)

instance IsString ReadPattern where
  fromString s = setPattern (fromString s)
        
instance Field_ ReadPattern where
  type Compound ReadPattern = Relative ReadChain
  p #. n = setPattern (p #. n)

instance Block_ ReadPattern where
  type Stmt ReadPattern = ReadMatch ReadPattern
  block_ bdy = 
    ReadPattern
      (patternDeclared
        (readPattern <$> readDecomp (block_ bdy))
        mempty)

instance Extend_ ReadPattern where
  type Extension ReadPattern = ReadDecomp ReadPattern
  type Ext ReadPattern = ReadPattern
  ReadPattern f # ReadDecomp d =
    ReadPattern
      (patternDeclared (readPattern <$> d) f)

newtype ReadDecomp a =
  ReadDecomp {
    readDecomp
     :: Multi (Declared Assoc (Option (Privacy These))) a
    }

instance Block_ (ReadDecomp a) where
  type Stmt (ReadDecomp a) = ReadMatch a
  block_ bdy =
    ReadDecomp
      (foldMap (Stores . fmap pure . readMatch) bdy)


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


newtype ReadMatch a =
  ReadMatch {
    readMatch ::
      Declared Assoc (Option (Privacy These)) a
    }

publicChain
 :: ReadChain -> ReadChain
publicChain (ReadChain f) =
  ReadChain (first (const pubTag) . f)
  where
    pubTag :: Either (Public ()) b
    pubTag = Left (Public ())

punMatch
 :: (Let_ s, Lhs s ~ ReadPath) => Pun ReadChain (Rhs s) -> s
punMatch = pun (setPath . publicChain) id

setMatch
 :: Declared Assoc (Privacy These) a -> ReadMatch a
setMatch d = ReadMatch (first pure d)

instance IsString a => IsString (ReadMatch a) where
  fromString s = punMatch (fromString s)

instance Field_ a => Field_ (ReadMatch a) where
  type Compound (ReadMatch a) =
    Pun (Relative ReadChain) (Compound a)
  p #. k = punMatch (p #. k)

instance Let_ (ReadMatch a) where
  type Lhs (ReadMatch a) = ReadPath
  type Rhs (ReadMatch a) = a
  ReadPath f #= a = setMatch (f a)
