{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, FlexibleInstances #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
import Goat.Lang.Parser (IDENTIFIER, parseIdentifier, Self(..))
import Goat.Repr.Pattern
  ( Assigns(..), wrapAssigns
  , Matches(..), wrapMatches
  , Declares(..), wrapLocal, wrapPublic
  , Bindings(..), Decompose, Components
  , bindPartsFromMatches, bindRemaining, ignoreRemaining
  , MonadBlock, Abs
  , (>>>=), Map, Text
  )
import qualified Data.Map as Map

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern =
  ReadPattern {
    readPattern
     :: forall m a . MonadBlock (Abs Components) m
     => a -> Bindings Declares Decompose m a
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

data ReadMatchPun p a = ReadMatchPun p a

punMatch
 :: ReadMatchPun ReadSelector a -> ReadMatchStmt a
punMatch (ReadMatchPun p a) = p #= a

instance
  IsString a => IsString (ReadMatchPun ReadSelector a)
  where
    fromString s =
      ReadMatchPun (fromString "" #. fromString s) (fromString s)

instance IsString a => IsString (ReadMatchStmt a) where
  fromString s = punMatch (fromString s)

instance Select_ a => Select_ (ReadMatchPun ReadSelector a) where
  type Selects (ReadMatchPun ReadSelector a) =
    ReadMatchPun (Either Self ReadSelector) (Selects a)
  type Key (ReadMatchPun ReadSelector a) = IDENTIFIER
  ReadMatchPun p a #. k =
    ReadMatchPun (p #. parseIdentifier k) (a #. parseIdentifier k)

instance Select_ a => Select_ (ReadMatchStmt a) where
  type Selects (ReadMatchStmt a) =
    ReadMatchPun (Either Self ReadSelector) (Selects a)
  type Key (ReadMatchStmt a) = IDENTIFIER
  p #. k = punMatch (p #. parseIdentifier k)

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
