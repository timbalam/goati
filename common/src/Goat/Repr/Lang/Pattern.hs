{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
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

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

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
        
instance Select_ ReadPattern where
  type Selects ReadPattern = Either Self ReadChain
  type Key ReadPattern = IDENTIFIER
  p #. n = setPattern (p #. n)

instance IsList ReadPattern where
  type Item ReadPattern = ReadMatchStmt ReadPattern
  fromList bdy = 
    ReadPattern
      (patternDeclared
        (readPattern <$> readPatternBlock (block_ bdy))
        mempty)
  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern = ReadPatternBlock ReadPattern
  ReadPattern f # ReadPatternBlock d =
    ReadPattern
      (patternDeclared (readPattern <$> d) f)

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a =
  ReadPatternBlock {
    readPatternBlock
     :: Multi (Declared Assoc (Option (Privacy These))) a
    }

instance IsList (ReadPatternBlock a) where
  type Item (ReadPatternBlock a) = ReadMatchStmt a
  fromList bdy =
    ReadPatternBlock
      (foldMap (Stores . fmap pure . readMatchStmt) bdy)
  toList = error "IsList (ReadPatternBlock a): toList"

{-
Match statement
---------------

A match statement is interpreted as a selector with associated pattern.
-}

newtype ReadMatchStmt a =
  ReadMatchStmt {
    readMatchStmt ::
      MatchSelection a
      -- Declared Assoc (Option (Privacy These)) a
    }

publicChain
 :: ReadChain -> ReadChain
publicChain (ReadChain f) =
  ReadChain (first (const pubTag) . f)
  where
    pubTag :: Either (Public ()) b
    pubTag = Left (Public ())
    

-- | A 'match pun' statement generates an assignment path with a syntacticly corresponding selector.
-- E.g. the match pun 'a.b.c' assigns the selector '.a.b.c'
-- to the path 'a.b.c'.
data MatchPun p a = MatchPun p a

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


punMatch
 :: (Let_ s, Lhs s ~ ReadPath) => Pun ReadChain (Rhs s) -> s
punMatch = pun (setPath . publicChain) id

setMatch
 :: Declared Assoc (Privacy These) a -> ReadMatchStmt a
setMatch d = ReadMatchStmt (first pure d)

instance IsString a => IsString (ReadMatchStmt a) where
  fromString s = punMatch (fromString s)

instance Field_ a => Field_ (ReadMatchStmt a) where
  type Compound (ReadMatchStmt a) =
    Pun (Relative ReadChain) (Compound a)
  p #. k = punMatch (p #. k)

instance Let_ (ReadMatchStmt a) where
  type Lhs (ReadMatchStmt a) = ReadPath
  type Rhs (ReadMatchStmt a) = a
  ReadPath f #= a = setMatch (f a)

{-
Path
----

A path is interpreted as a function for injecting a sub-selection into a match selection.
-}

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


-- | Binding 
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

