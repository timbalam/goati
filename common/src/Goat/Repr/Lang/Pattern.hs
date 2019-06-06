{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, FlexibleInstances #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( IDENTIFIER, parseIdentifier, Self(..)
  , PATTERN, parsePattern
  , PATH, parsePath
  , SELECTOR, parseSelector
  , MATCHSTMT, parseMatchStmt
  , PATTERNBLOCK, parsePatternBlock
  )
import Goat.Repr.Pattern
import Data.Function (on)
import qualified Data.Map as Map

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern =
  ReadPattern {
    readPattern
     :: forall m a . MonadBlock AmbigBlock m
     => a -> Bindings Declares AmbigCpts m a
    }

patternProof :: PATTERN -> ReadPattern
patternProof = parsePattern

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
  type Item ReadPattern =
    ReadMatchStmt (Either ReadPattern ReadPattern)
  fromList bdy =
      ReadPattern
        (ignoreRemaining .
        bindPartsFromMatches
          (either readPattern readPattern <$>
            readPatternBlock (fromList bdy)))
  
  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern =
    ReadPatternBlock (Either ReadPattern ReadPattern)
  ReadPattern f # ReadPatternBlock m =
    ReadPattern
      (\ a -> 
        bindRemaining f
          (bindPartsFromMatches
            (either readPattern readPattern <$> m)
            a))

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

data ReadPatternBlock a =
  ReadPatternBlock { readPatternBlock :: Matches a }

proofPatternBlock
 :: PATTERNBLOCK a -> ReadPatternBlock (Either ReadPattern a)
proofPatternBlock = parsePatternBlock id

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

proofMatchStmt
  :: MATCHSTMT a -> ReadMatchStmt (Either ReadPattern a)
proofMatchStmt = parseMatchStmt id

data ReadMatchPun =
  ReadMatchPun (forall a. Path_ a => a) ReadSelector

proofMatchPun :: PATH -> ReadMatchPun 
proofMatchPun = parsePath

punMatch :: Path_ a => ReadMatchPun -> ReadMatchStmt (Either a b)
punMatch (ReadMatchPun a (ReadSelector f)) =
  ReadMatchStmt (f (Leaf (Left a)))

instance IsString ReadMatchPun where
  fromString s =
    ReadMatchPun (fromString s) (fromString "" #. fromString s)

instance Path_ a => IsString (ReadMatchStmt (Either a b)) where
  fromString s = punMatch (fromString s)

instance Select_ ReadMatchPun where
  type Selects ReadMatchPun = Either Self ReadMatchPun
  type Key ReadMatchPun = IDENTIFIER
  Left s #. k =
    ReadMatchPun
      (fromString "" #. parseIdentifier k) (Left s #. k)
  Right (ReadMatchPun p a) #. k =
    ReadMatchPun (p #. parseIdentifier k) (Right a #. k)

instance Path_ a => Select_ (ReadMatchStmt (Either a b)) where
  type Selects (ReadMatchStmt (Either a b)) =
    Either Self ReadMatchPun
  type Key (ReadMatchStmt (Either a b)) = IDENTIFIER
  p #. k = punMatch (p #. k)

instance Assign_ (ReadMatchStmt (Either a b)) where
  type Lhs (ReadMatchStmt (Either a b)) = ReadSelector
  type Rhs (ReadMatchStmt (Either a b)) = b
  ReadSelector f #= b = ReadMatchStmt (f (Leaf (Right b)))

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector =
  ReadSelector {
    readSelector :: forall a . Assigns (Map Text) a -> Matches a
    }

proofSelector :: SELECTOR -> ReadSelector
proofSelector = parseSelector

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

pathProof :: PATH -> ReadPath
pathProof = parsePath

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
