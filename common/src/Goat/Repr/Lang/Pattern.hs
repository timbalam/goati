{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, FlexibleInstances #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( IDENTIFIER, parseIdentifier, Self(..)
  , PATTERN, parsePattern
  , PATH, parsePath
  , CanonPath_, CanonPath, CanonSelector
  , SELECTOR, parseSelector
  , MATCHSTMT, parseMatchStmt
  , PATTERNBLOCK, parsePatternBlock
  )
import Goat.Lang.Parser.Path (NAString, Void)
import Goat.Lang.Error (ExprCtx(..))
import Goat.Repr.Pattern
import Goat.Util ((<&>))
import Data.Function (on)
import qualified Data.Map as Map
import Data.Map (Map)

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern b
  = ReadPattern 
  { readPattern
     :: forall m a
      . MonadBlock (BlockCpts Text) m
     => a
     -> b
     -> Bindings
          (Assocs (VarTrail Text)) (TagCpts Text) m a
  }

patternProof
 :: PATTERN -> ReadPattern 
patternProof = parsePattern

setPattern
 :: VarTrail Text -> ReadPattern
setPattern ks
  = ReadPattern
      (\ a -> Define (Assocs [(ks, return a)]))

instance IsString ReadPattern where
  fromString s
    = setPattern (readPath (fromString s))

instance Select_ ReadPattern where
  type Selects ReadPattern = Either Self ReadPath
  type Key ReadPattern = IDENTIFIER
  p #. k = setPattern (readPath (p #. k))

instance IsList ReadPattern where
  type
    Item ReadPattern
    = ReadMatchStmt
        (Either (VarTrail Text) ReadPattern)
  fromList bdy
    = ReadPattern
        (ignoreRemaining
          . bindPartsFromAssocs
              (either
                (readPattern . setPattern)
                readPattern
               <$> readPatternBlock (fromList bdy)))

  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern
    = ReadPatternBlock
        (Either (VarTrail Text) ReadPattern)
  ReadPattern f # ReadPatternBlock asc
    = ReadPattern
        (bindRemaining f
          . bindPartsFromAssocs
              (either
                (readPattern . setPattern)
                readPattern
                <$> asc))

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a
  = ReadPatternBlock
  { readPatternBlock :: Assocs [Text] a }

proofPatternBlock
 :: PATTERNBLOCK a
 -> ReadPatternBlock (Either (VarTrail Text) a)
proofPatternBlock = parsePatternBlock id

instance
  IsList (ReadPatternBlock a) where
  type Item (ReadPatternBlock a) = ReadMatchStmt a
  fromList bdy = ReadPatternBlock (coerce bdy)
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
  { readMatchStmt :: Assocs [Text] a }

proofMatchStmt
 :: MATCHSTMT a
 -> ReadMatchStmt (Either (VarTrail Text) a)
proofMatchStmt = parseMatchStmt id

punMatch
 :: VarTrail Text
 -> ReadMatchStmt (Either (VarTrail Text) a)
punMatch vks
  = ReadMatchStmt (Assocs [(toTrail p, Left p)])
  where
  toTrail (Left (Local ks)) = ks
  toTrail (Right (Public ks)) = ks

instance
  IsString (ReadMatchStmt (Either ReadPath b)) where
  fromString s
    = punMatch (readPath (fromString s))

instance
  Select_ (ReadMatchStmt (Either ReadPath a))
  where
  type Selects (ReadMatchStmt (Either ReadPath a))
    = Either Self ReadPath
  type Key (ReadMatchStmt (Either ReadPath a))
    = IDENTIFIER
  p #. k = punMatch (readPath (p #. k))

instance
  Assign_ (ReadMatchStmt (Either a b)) where
  type Lhs (ReadMatchStmt (Either a b))
    = ReadSelector
  type Rhs (ReadMatchStmt (Either a b)) = b
  s #= b
    = ReadMatchStmt
        (Assoc [(readSelector s, Right b)])

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector
 = ReadSelector ([Text] -> [Text])
 
readSelector :: ReadSelector -> [Text]
readSelector (ReadSelector f) = f []

proofSelector :: SELECTOR -> ReadSelector
proofSelector = parseSelector

instance Select_ ReadSelector where
  type Selects ReadSelector
    = Either Self ReadSelector
  type Key ReadSelector = IDENTIFIER
  Left Self #. k
    = ReadSelector (parseIdentifier k:)
  
  Right (ReadSelector f) #. k
    = ReadSelector (f . (parseIdentifier k:))

{-
Path
----

A path is interpreted as a function for injecting a sub-declaration into a larger declaration.
-}

type VarTrail k
  = Either (Local [k]) (Public [k])

newtype ReadPath = ReadPath ([Text] -> VarTrail Text)

readPath :: ReadPath -> VarTrail Text
readPath (ReadPath f) = f []

pathProof :: PATH -> ReadPath
pathProof = parsePath

instance IsString ReadPath where
  fromString s
    = ReadPath (Left . Local . (fromString s:))

instance Select_ ReadPath where
  type Selects ReadPath = Either Self ReadPath
  type Key ReadPath = IDENTIFIER
  Left Self #. k
    = ReadPath
        (Right . Public . (parseIdentifier k:))
  
  Right (ReadPath f) #. k
    = ReadPath (f . (parseIdentifier k:))
{-
-- Generate a local pun for each bound public path.

data ReadPathPun
  = ReadPublicShadowLocal
      (forall x . Selector_ x => x)
      -- ^ local shadow value
      ReadPath -- ^ public path
  | ReadLocal ReadPath

proofPath :: PATH -> ReadPathPun
proofPath = parsePath

pathPunStmt
 :: Selector_ a
 => ReadContext CanonPath ReadPathPun
 -> ReadPattern (ShadowVar a)
pathPunStmt (ReadLocal p)
  = ReadPattern
      (transBindings 
        (..
        . readPattern (setPattern p))
      
pathPunStmt
  (ReadPublicWithLocalShadow a lp (ReadContext p pp))
  = ReadPatternWithShadowStmts
      (ReadStmt
        (\ an
         -> readPattern
              (setPatternWithContext 
                (ReadContext p lp))
              an
              id
              (Left a)))
      (setPattern pp)

instance IsString ReadPathPun where
  fromString s = ReadLocal (fromString)

instance Select_ ReadPathPun where
  type Selects ReadPathPun
    = Either Self ReadPathPun
  type Key ReadPathPun = IDENTIFIER
  Left Self #. k
    = ReadPublicShadowLocal
        (fromString "" #. k)
        (Left Self #. k)
  
  Right (ReadLocal p) = ReadLocal (p #. k)
  Right (ReadPublicShadowLocal s p)
    = ReadPublicShadowLocal
        (Right s #. k) (Right p #. k)

-- 
data ReadContext a b = ReadContext a b

proofPathContext
 :: PATH -> ReadContext CanonPath ReadPath
proofPathContext = parsePath

proofSelectorContext
 :: SELECTOR
 -> ReadContext CanonSelector ReadSelector
proofSelectorContext = parseSelector

instance
  (IsString a, IsString b)
   => IsString (ReadContext a b) where
  fromString s
    = ReadContext (fromString s) (fromString s)

instance
  (IsString b, Select_ c)
   => Select_ (ReadContext (CanonPath_ a b) c)
  where
  type Selects (ReadContext (CanonPath_ a b) c)
    = ReadContext
        (CanonPath_ (Either Self b) b) (Selects c)
  type Key (ReadContext (CanonPath_ a b) c)
    = IDENTIFIER
  ReadContext a b #. k
    = ReadContext (a #. k) (b #. parseIdentifier k)
-}
