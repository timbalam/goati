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
     :: forall m a . MonadBlock (Abs Components) m 
     => a
     -> Bindings Declares (Components ()) m a
    }

setPattern :: ReadPath -> ReadPattern
setPattern (ReadPath f) = ReadPattern (f . pure)

instance IsString ReadPattern where
  fromString s = setPattern (fromString s)
        
instance Select_ ReadPattern where
  type Selects ReadPattern = Either Self ReadPath
  type Key ReadPattern = IDENTIFIER
  p #. n = setPattern (p #. fromIdentifier n)

instance IsList ReadPattern where
  type Item ReadPattern = ReadMatchStmt ReadPattern
  fromList bdy =
    case block_ bdy of
      ReadPatternBlock d ->
        ReadPattern
          (ignoreRemaining .
            bindPartsFromMatches (readPattern <$> d))
  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern = ReadPatternBlock ReadPattern
  ReadPattern f # ReadPatternBlock d =
    ReadPattern
      (bindRemaining f .
        bindPartsFromMatches (readPattern <$> d))

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
 :: Assign_ s => ReadMatchPun (Lhs s) (Rhs s) -> s
punMatch (ReadMatchPun a b) = a #= b 

instance
  (Field_ p, IsString a) => IsString (ReadMatchPun p a)
  where
    fromString s =
      ReadMatchPun
        (fromString "" #. fromString s)
        (fromString n)

instance IsString a => IsString (ReadMatchStmt a) where
  fromString s = punMatch (fromString s)

instance
  (Select_ p, Select_ a) => Select_ (ReadMatchPun p a)
  where
    type Selects (ReadMatchPun p a) =
      ReadMatchPun (Selects p) (Selects a)
    type Key (ReadMatchPun p a) = IDENTIFIER
    MatchPun p a #. k =
      MatchPun (p #. fromIdentifier k) (a #. fromIdentifier k)

instance (Select_ a) => Field_ (ReadMatchStmt a) where
  type Selects (ReadMatchStmt a) =
    ReadMatchPun (Either Self ReadSelector) (Selects a)
  type Key (ReadMatchStmt a) = IDENTIFIER
  p #. k = punMatch (p #. fromIdentifier k)

instance Let_ (ReadMatchStmt a) where
  type Lhs (ReadMatchStmt a) = ReadSelector
  type Rhs (ReadMatchStmt a) = a
  ReadSelector f #= a = ReadMatch (f (Leaf [a]))

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector =
  ReadSelector {
    readSelector
     :: forall a . Assigns a -> Matches a
    }

instance IsString ReadSelector where
  fromString s =
    ReadSelector
      (wrapMatches . Map.singleton (fromString s) . pure)

instance Field_ ReadSelector where
  type Selects ReadSelector = Either Self ReadSelector
  type Key ReadSelector = IDENTIFIER
  Left Self #. k =
    ReadSelector
      (wrapMatches . Map.singleton (fromIdentifier k) . pure)
  Right (ReadSelector f) #. k =
    ReadSelector
      (f . wrapAssigns . Map.singleton (fromIdentifier k))

