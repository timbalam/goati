{-# LANGUAGE TypeFamilies, RankNTypes, FlexibleContexts, FlexibleInstances, LambdaCase #-}
module Goat.Repr.Lang.Pattern where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( IDENTIFIER, parseIdentifier, Self(..)
  , PATTERN, parsePattern
  , PATH, parsePath
  --, CanonPath_, CanonPath, CanonSelector
  , SELECTOR, parseSelector
  , MATCHSTMT, parseMatchStmt
  , PATTERNBLOCK, parsePatternBlock
  )
import Goat.Lang.Parser.Path (NAString(..))
import Goat.Repr.Pattern
import Goat.Util ((<&>), (...))
import Bound ((>>>=))
import Control.Monad.Trans (lift)
import Data.Coerce (coerce)
import Data.Function (on)
import qualified Data.List.NonEmpty as NonEmpty
--import qualified Data.Map as Map
--import Data.Map (Map)

{-
Pattern
-------

A syntactic pattern is read as a function that associates a right hand side value with a set of bindings.
-}

newtype ReadPattern
  = ReadPattern 
  { readPattern
     :: forall m a b
      . MonadBlock (Block (AnnCpts [b]) Ident) m
     => a
     -> Bindings
          (AssocViews (Trail Ident))
          (AnnCpts [Trail Ident] Ident)
          m
          a
  }

patternProof
 :: PATTERN -> ReadPattern 
patternProof = parsePattern

setPattern
 :: View (Trail Ident) -> ReadPattern
setPattern vt
  = ReadPattern
      (\ a
       -> Define (Assocs [declare vt (return a)]))
  where
  declare
   :: View (Trail k)
   -> a
   -> (Trail k, View a)
  declare (Tag (Left (Local t))) a
    = (t, Tag (Left (Local a)))
  declare (Tag (Right (Public t))) a
    = (t , Tag (Right (Public a)))

instance IsString ReadPattern where
  fromString s
    = setPattern (readPath (fromString s))

instance Select_ ReadPattern where
  type Selects ReadPattern = Either Self ReadPath
  type Key ReadPattern = ReadKey
  p #. k = setPattern (readPath (p #. k))

instance IsList ReadPattern where
  type
    Item ReadPattern
    = ReadMatchStmt
        (Either (View (Trail Ident)) ReadPattern)
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
        (Either (View (Trail Ident)) ReadPattern)
  ReadPattern f # ReadPatternBlock b
    = ReadPattern
        (bindRemaining f
          . bindPartsFromAssocs
              (either
                (readPattern . setPattern)
                readPattern
               <$> b))

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a
  = ReadPatternBlock
  { readPatternBlock :: Assocs (Trail Ident) a }

proofPatternBlock
 :: PATTERNBLOCK a
 -> ReadPatternBlock
      (Either (View (Trail Ident)) a)
proofPatternBlock = parsePatternBlock id

instance
  IsList (ReadPatternBlock a) where
  type Item (ReadPatternBlock a) = ReadMatchStmt a
  fromList bdy
    = ReadPatternBlock (foldMap readMatchStmt bdy)
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
  { readMatchStmt :: Assocs (Trail Ident) a }

proofMatchStmt
 :: MATCHSTMT a
 -> ReadMatchStmt (Either (View (Trail Ident)) a)
proofMatchStmt = parseMatchStmt id

punMatch
 :: View (Trail Ident)
 -> ReadMatchStmt (Either (View (Trail Ident)) a)
punMatch vt
  = ReadMatchStmt
      (Assocs [(toTrail vt, pure (Left vt))])
  where
  toTrail (Tag (Left (Local t))) = t
  toTrail (Tag (Right (Public t))) = t

instance
  IsString
    (ReadMatchStmt 
      (Either (View (Trail Ident)) b)) 
  where
  fromString s
    = punMatch (readPath (fromString s))

instance
  Select_
    (ReadMatchStmt
      (Either (View (Trail Ident)) a))
  where
  type
    Selects
      (ReadMatchStmt
        (Either (View (Trail Ident)) a))
    = Either Self ReadPath
  type
    Key
      (ReadMatchStmt
        (Either (View (Trail Ident)) a))
    = ReadKey
  p #. k = punMatch (readPath (p #. k))

instance
  Assign_ (ReadMatchStmt (Either a b)) where
  type Lhs (ReadMatchStmt (Either a b))
    = ReadSelector
  type Rhs (ReadMatchStmt (Either a b)) = b
  s #= b
    = ReadMatchStmt
        (Assocs [(readSelector s, pure (Right b))])

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector
 = ReadSelector ([Ident] -> Trail Ident)
 
readSelector :: ReadSelector -> Trail Ident
readSelector (ReadSelector f) = f []

proofSelector :: SELECTOR -> ReadSelector
proofSelector = parseSelector

instance Select_ ReadSelector where
  type Selects ReadSelector
    = Either Self (NAString ReadSelector)
  type Key ReadSelector = ReadKey
  Left Self #. ReadKey k
    = ReadSelector (k NonEmpty.:|)
  
  Right (NAString (ReadSelector f)) #. ReadKey k
    = ReadSelector (f . (k :))

{-
Path
----

A path is interpreted as a function for injecting a sub-declaration into a larger declaration.
-}

newtype ReadPath
  = ReadPath ([Ident] -> View (Trail Ident))

readPath :: ReadPath -> View (Trail Ident)
readPath (ReadPath f) = f []

pathProof :: PATH -> ReadPath
pathProof = parsePath

instance IsString ReadPath where
  fromString s
    = ReadPath
        (Tag
          . Left
          . Local
          . (readKey (fromString s) NonEmpty.:|))

instance Select_ ReadPath where
  type Selects ReadPath = Either Self ReadPath
  type Key ReadPath = ReadKey
  Left Self #. ReadKey k
    = ReadPath
        (Tag
          . Right
          . Public
          . (k NonEmpty.:|))
  
  Right (ReadPath f) #. ReadKey k
    = ReadPath (f . (k :))

-- Key

newtype ReadKey = ReadKey { readKey :: Ident }

proofKey :: IDENTIFIER -> ReadKey
proofKey = parseIdentifier

instance IsString ReadKey where
  fromString s = ReadKey (Ident (fromString s))

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
