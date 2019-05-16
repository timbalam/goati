{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, FlexibleInstances #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
import Goat.Lang.Parser (IDENTIFIER, parseIdentifier, Self(..))
import Goat.Repr.Pattern
  ( Assigns(..), wrapAssigns
  , Matches(..), wrapMatches
  , Declares(..), wrapLocal, wrapPublic
  --, Local(..), Public(..), Match(..)
  , Bindings(..), Components
  -- , Extend(..), Pattern
  , bindPartsFromMatches, bindRemaining, ignoreRemaining
  , MonadBlock, Abs
  , (>>>=), Map, Text
  )
import qualified Data.Map as Map
-- import Data.Align (Align(..))
-- import Data.Bifunctor (first)
-- import Data.Biapplicative (bipure)
-- import Data.List.NonEmpty (NonEmpty(..))
-- import Data.These (These(..), these, mergeTheseWith)
-- import Data.Semigroup ((<>), Option)
-- import Data.Void (absurd)

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern =
  ReadPattern {
    readPattern
     :: forall m a . MonadBlock (Abs Components) m
     => a -> Bindings Declares (Components ()) m a
    }

setPattern :: ReadPath -> ReadPattern
setPattern (ReadPath f) =
  ReadPattern (Define . f . Leaf . pure)        

instance IsString ReadPattern where
  fromString s = setPattern (fromString s)

instance Select_ ReadPattern where
  type Selects ReadPattern = Either Self ReadPath
  type Key ReadPattern = IDENTIFIER
  p #. k = setPattern (p #. k)

instance IsList ReadPattern where
  type Item ReadPattern = ReadMatchStmt ReadPattern
  fromList bdy =
    case fromList bdy of
      ReadPatternBlock d ->
        ReadPattern
          (ignoreRemaining .
          bindPartsFromMatches (readPattern <$> d))
  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern = ReadPatternBlock ReadPattern
  ReadPattern f # ReadPatternBlock d =
    ReadPattern
      (\ a -> 
        bindRemaining f
          (bindPartsFromMatches (readPattern <$> d) a))

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a =
  ReadPatternBlock { readPatternBlock :: Matches a }

instance IsList (ReadPatternBlock a) where
  type Item (ReadPatternBlock a) = ReadMatchStmt a
  fromList bdy =
    ReadPatternBlock (foldMap readMatchStmt bdy)
  toList = error "IsList (ReadPatternBlock a): toList"

{-
Match statement
---------------

A match statement is interpreted as a selector with associated pattern.
The 'match pun' statement generates an assignment path along with a syntactically corresponding selector.
E.g. the match pun 'a.b.c' assigns the path 'a.b.c'
to selector '.a.b.c'.
-}

newtype ReadMatchStmt a =
  ReadMatchStmt { readMatchStmt :: Matches a }

data ReadPun p a = ReadPun p a

pun
 :: Assign_ s => ReadPun (Lhs s) (Rhs s) -> s
pun (ReadPun a b) = a #= b 

instance IsString a => IsString (ReadPun ReadSelector a) where
  fromString s =
    ReadPun (fromString "" #. fromString s) (fromString s)

instance IsString a => IsString (ReadMatchStmt a) where
  fromString s = pun (fromString s)

instance Select_ a => Select_ (ReadPun ReadSelector a) where
  type Selects (ReadPun ReadSelector a) =
    ReadPun (Either Self ReadSelector) (Selects a)
  type Key (ReadPun ReadSelector a) = IDENTIFIER
  ReadPun p a #. k =
    ReadPun (p #. parseIdentifier k) (a #. parseIdentifier k)

instance Select_ a => Select_ (ReadMatchStmt a) where
  type Selects (ReadMatchStmt a) =
    ReadPun (Either Self ReadSelector) (Selects a)
  type Key (ReadMatchStmt a) = IDENTIFIER
  p #. k = pun (p #. parseIdentifier k)

instance Assign_ (ReadMatchStmt a) where
  type Lhs (ReadMatchStmt a) = ReadSelector
  type Rhs (ReadMatchStmt a) = a
  ReadSelector f #= a = ReadMatchStmt (f (Leaf a))

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector =
  ReadSelector {
    readSelector :: forall a . Assigns (Map Text) a -> Matches a
    }

instance IsString ReadSelector where
  fromString s =
    ReadSelector
      (wrapMatches . Map.singleton (fromString s))

instance Select_ ReadSelector where
  type Selects ReadSelector = Either Self ReadSelector
  type Key ReadSelector = IDENTIFIER
  Left Self #. k =
    ReadSelector
      (wrapMatches . Map.singleton (parseIdentifier k))
  Right (ReadSelector f) #. k =
    ReadSelector
      (f . wrapAssigns . Map.singleton (parseIdentifier k))

{-
Path
----

A path is interpreted as a function for injecting a sub-declaration into a larger declaration.
-}

newtype ReadPath =
  ReadPath {
    readPath :: forall a . Assigns (Map Text) a -> Declares a
    }

instance IsString ReadPath where
  fromString s =
    ReadPath (wrapLocal . Map.singleton (fromString s))

instance Select_ ReadPath where
  type Selects ReadPath = Either Self ReadPath
  type Key ReadPath = IDENTIFIER
  Left Self #. k =
    ReadPath
      (wrapPublic . Map.singleton (parseIdentifier k))
  
  Right (ReadPath f) #. k =
    ReadPath
      (f . wrapAssigns . Map.singleton (parseIdentifier k))
