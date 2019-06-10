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
import Data.Map (Map)

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern
  = ReadPattern 
  { readPattern
     :: forall m a
      . MonadBlock BlockCpts m
     => a
     -> Bindings
          (Inside (Ambig StmtMap) Declares) 
          (AmbigCpts StmtMap)
          m
          a
  }

type StmtMap = (,) Map Int PATH

patternProof :: PATTERN -> State Int ReadPattern
patternProof = parsePattern

setPattern
 :: ReadPathContext ReadPath -> State Int ReadPattern
setPattern (ReadPathContext p (ReadPath f))
  = State
      (\ i
       -> ( setPatternWith (Map.singleton i, p)
          , i+1
          ))
  where
  setPatternWith s =
    ReadPattern . Define
      . Inside . f . Leaf
      . Ambig . (,) s  . pure

instance IsString (State Int ReadPattern) where
  fromString s = setPattern (fromString s)

instance Select_ (State Int ReadPattern) where
  type Selects (State Int ReadPattern)
    = Either Self ReadPath
  type Key (State Int ReadPattern) = IDENTIFIER
  p #. k = setPattern (p #. k)

instance IsList (State Int ReadPattern) where
  type Item (State Int ReadPattern)
    = State Int
        (ReadMatchStmt
          (Either
            (State Int ReadPattern)
            (State Int ReadPattern)))
  fromList bdy
    = traverse
        (either readPattern readPattern)
        (readPatternBlock (fromList bdy))
   <&> ReadPattern
     . ignoreRemaining
     . bindPartsFromMatches
  
  toList = error "IsList ReadPattern: toList"

instance Extend_ (State Int ReadPattern) where
  type Extension (State Int ReadPattern)
    = ReadPatternBlock
        (Either
          (State Int ReadPattern)
          (State Int ReadPattern))
  sp # ReadPatternBlock m
    = do
      ReadPattern f <- sp
      m'
       <- traverse (either readPattern readPattern) m
      return
        (ReadPattern
          (\ a
           -> bindRemaining f
                (bindPartsFromMatches m' a))

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

data ReadPatternBlock a
  = ReadPatternBlock
  { readPatternBlock
     :: Inside (Ambig StmtMap) Matches a
  }

proofPatternBlock
 :: PATTERNBLOCK a
 -> ReadPatternBlock (Either ReadPattern a)
proofPatternBlock = parsePatternBlock id

instance
  IsList (ReadPatternBlock a)
  where
  type Item (ReadPatternBlock a)
    = State Int (ReadMatchStmt a)
  fromList bdy
    = ReadPatternBlock
        (foldMap
          readMatchStmt
          (execState (sequenceA bdy) 0))
  toList
    = error "IsList (ReadPatternBlock a): toList"

{-
Match statement
---------------

A match statement is interpreted as a selector with associated pattern.
The 'match pun' statement generates an assignment path along with a syntactically corresponding selector.
E.g. the match pun 'a.b.c' assigns the path 'a.b.c'
to selector '.a.b.c'.
-}

newtype ReadMatchStmt a
  = ReadMatchStmt
  { readMatchStmt
     :: Inside (Ambig StmtMap) Matches a
  }

proofMatchStmt
 :: MATCHSTMT a
 -> State Int
      (ReadMatchStmt
        (Either (State Int ReadPattern) a))
proofMatchStmt = parseMatchStmt id

data ReadMatchPun
  = ReadMatchPun
      (forall a. Path_ a => a)
      ReadSelector

proofMatchPun :: PATH -> ReadMatchPun 
proofMatchPun = parsePath

punMatch
 :: Path_ a
 => ReadPathContext ReadMatchPun
 -> State Int (ReadMatchStmt (Either a b))
punMatch
  (ReadPathContext p
    (ReadMatchPun a (ReadSelector f)))
  = State 
      (\ i
       -> (punMatchWith (Map.singleton i p), i+1))
  where
  punMatchWith s
    = ReadMatchStmt
        (Inside
          (f (Leaf (Ambig (s, pure (Left a))))))

instance IsString ReadMatchPun where
  fromString s
    = ReadMatchPun
        (fromString s)
        (fromString "" #. fromString s)

instance
  Path_ a
   => IsString
        (State Int (ReadMatchStmt (Either a b)))
  where
  fromString s = punMatch (fromString s)

instance Select_ ReadMatchPun where
  type Selects ReadMatchPun
    = Either Self ReadMatchPun
  type Key ReadMatchPun = IDENTIFIER
  Left s #. k
    = ReadMatchPun
        (fromString "" #. parseIdentifier k)
        (Left s #. k)
  
  Right (ReadMatchPun p a) #. k
    = ReadMatchPun
        (p #. parseIdentifier k)
        (Right a #. k)

instance
  Path_ a
   => Select_
        (State Int (ReadMatchStmt (Either a b)))
  where
  type
    Selects (State Int (ReadMatchStmt (Either a b)))
    = Either Self ReadMatchPun
  type Key (ReadMatchStmt (Either a b)) = IDENTIFIER
  p #. k = punMatch (p #. k)

instance
  Assign_ (State Int (ReadMatchStmt (Either a b))) 
  where
  type Lhs (State Int (ReadMatchStmt (Either a b)))
    = ReadPathContext ReadSelector
  type Rhs (State Int (ReadMatchStmt (Either a b)))
    = b
  ReadPathContext p (ReadSelector f) #= b
    = State
        (\ i
         -> assignMatchWith (Map.singleton i p) b)
    where
    assignMatchWith s
      = ReadMatchStmt
          (Inside
            (f
              (Leaf (Ambig (s, pure (Right b))))))

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector
  = ReadSelector
  { readSelector
     :: forall a
      . Assigns (Map Text) a
     -> Matches a
  }

proofSelector :: SELECTOR -> ReadSelector
proofSelector = parseSelector

instance IsString ReadSelector where
  fromString s
    = ReadSelector
        (wrapMatches
          . Map.singleton (fromString s))

instance Select_ ReadSelector where
  type Selects ReadSelector
    = Either Self ReadSelector
  type Key ReadSelector = IDENTIFIER
  Left Self #. k
    = ReadSelector
        (wrapMatches
          . Map.singleton (parseIdentifier k))
  
  Right (ReadSelector f) #. k
    = ReadSelector
        (f
          . wrapAssigns
          . Map.singleton (parseIdentifier k))

{-
Path
----

A path is interpreted as a function for injecting a sub-declaration into a larger declaration.
-}

newtype ReadPath
  = ReadPath
  { readPath
     :: forall a
      . Assigns (Map Text) a -> Declares a
  }

pathProof :: PATH -> ReadPath
pathProof = parsePath

instance IsString ReadPath where
  fromString s
    = ReadPath
        (wrapLocal . Map.singleton (fromString s))

instance Select_ ReadPath where
  type Selects ReadPath = Either Self ReadPath
  type Key ReadPath = IDENTIFIER
  Left Self #. k
    = ReadPath
        (wrapPublic
          . Map.singleton (parseIdentifier k))
  
  Right (ReadPath f) #. k
    = ReadPath
        (f
          . wrapAssigns
          . Map.singleton (parseIdentifier k))

-- | Path with context
data ReadPathContext a
  = ReadPathContext PATH a

instance IsString a => IsString (ReadPathContext a)
  where
  fromString s
    = ReadPathContext (fromString s) (fromString s)

instance
  (Select_ a, IsString (Selects a))
   => Select_ ReadPathContext
  where
  type Selects (ReadPathContext a)
    = Either Self (ReadPathContext (Selects a))
  type Key (ReadPathContext a) = IDENTIFIER
  Left Self #. k
    = ReadPathContext
        (Left Self #. k)
        (fromString "" #. parseIdentifier k)
  Right (ReadPathContext a b) #. k
    = ReadPathContext (Right a #. k) (b #. k)
