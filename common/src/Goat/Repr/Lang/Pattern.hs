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
type Ctxs a = (,) [ExprCtx a]

newtype ReadPattern b
  = ReadPattern 
  { readPattern
     :: forall m a
      . MonadBlock (BlockCpts (Ctxs CanonSelector)) m
     => a
     -> b
     -> Bindings
          (Inside
            (Ambig
              ((,,) [ExprCtx CanonPath] b) Assoc)
          (Cpts (Ctxs CanonSelector))
          m
          a
  }

patternProof
 :: PATTERN -> ReadPattern 
patternProof = parsePattern

setPattern
 :: ReadContext CanonPath ReadPath -> ReadPattern
setPattern (ReadContext p (ReadPath f))
  = ReadPattern
      (\ a
       -> Define
            (Inside
              (Ambig
                . pure
                . (,) [PathCtx p]
               <$> f (Leaf (return a)))))

instance IsString ReadPattern where
  fromString s = setPattern (fromString s)

instance Select_ ReadPattern where
  type Selects ReadPattern
    = ReadContext
        (CanonPath_
          (Either Self IDENTIFIER) IDENTIFIER)
        (Either Self ReadPath)
  type Key ReadPattern
    = IDENTIFIER
  p #. k = setPattern (p #. k)

instance IsList ReadPattern where
  type
    Item ReadPattern
    = ReadMatchStmt
        (Selector, Either ReadPattern ReadPattern)
  fromList bdy
    = ReadPattern
        (ignoreRemaining
          . bindPartsFromAssocs
              (readPatternBlockWithContext
                (either
                  readPattern
                  readPattern)
                (fromList bdy)))

  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern
    = ReadPatternBlock
        (Either ReadPattern ReadPattern)
  ReadPattern f # pb
    = ReadPattern
        (bindRemaining f
          . bindPartsFromAssocs
              (readPatternBlockWithContext
                (either readPattern readPattern)
                pb))

readPatternBlockWithContext
 :: (a
     -> b
     -> Bindings
          (Inside (Ambig (Declares (Ctxs u)) f))
          p
          m
          b)
 -> PatternBlock (Int, (CanonSelector, a))
 -> b
 -> Bindings (Inside (AmbigDecl (Ctxs u)) f) p m b
readPatternBlockWithContext f (PatternBlock m)
  = toAmbigCtx f <$> m
  where
  toAmbigCtx f (i, (s, a))
    = Ambig
        ( [StmtCtx i (PathCtx s)]
        , transBindings
            (hoistInside
              (hoistAmbig
                (first (StmtCtx i))))
            . f a
        )

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a
  = ReadPatternBlock
  { readPatternBlock :: Assocs (NonEmpty a) }

proofPatternBlock
 :: PATTERNBLOCK a
 -> ReadPatternBlock
      (Int, (CanonSelector, Either ReadPattern a))
proofPatternBlock = parsePatternBlock id

instance
  IsList (ReadPatternBlock (Int, a)) where
  type Item (ReadPatternBlock (Int, a)
    = ReadMatchStmt a
  fromList bdy
    = ReadPatternBlock
        (case foldStmts bdy of
        Inside kv -> kv)
    where
    foldStmts
      = foldMap id
          . mapWithIndex
            (\ i m
              -> Inside
                  (pure . ((,) i)
                   <$> readMatchStmt m))
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
  { readMatchStmt :: Assocs a }

proofMatchStmt
 :: MATCHSTMT a
 -> ReadMatchStmt
      (CanonSelector, Either ReadPattern a)
proofMatchStmt = parseMatchStmt id

data ReadMatchPun a
  = ReadMatchPun
      (forall x. Path_ x => x)
      (ReadContext a ReadSelector)

proofMatchPun :: PATH -> ReadMatchPun CanonSelector
proofMatchPun = parsePath

punMatch
 :: Path_ a
 => ReadMatchPun p
 -> ReadMatchStmt (p, Either a b)
punMatch
  (ReadMatchPun a (ReadContext p (ReadSelector f)))
  = ReadMatchStmt
      (Inside (f (Leaf (p, Left a))))

instance
  IsString b
   => IsString (ReadMatchPun (CanonPath_ a b)) where
  fromString s
    = ReadMatchPun
        (fromString s)
        (fromString "" #. fromString s)

instance
  Path_ a
   => IsString
        (ReadMatchStmt (CanonSelector, Either a b))
  where
  fromString s = punMatch (fromString s)

instance
  IsString b
   => Select_ (ReadMatchPun (CanonPath_ a b)) where
  type Selects (ReadMatchPun (CanonPath_ a b))
    = Either Self
        (ReadMatchPun (CanonPath_ (Either Self b) b))
  type Key (ReadMatchPun (CanonPath_ a b))
    = IDENTIFIER
  Left s #. k
    = ReadMatchPun
        (fromString "" #. parseIdentifier k)
        (ReadContext (fromString "") (Left s) #. k)
  
  Right (ReadMatchPun p (ReadContext a b)) #. k
    = ReadMatchPun
        (p #. parseIdentifier k)
        (ReadContext a (Right b)
         #. parseIdentifier k)

instance
  Path_ a
   => Select_
        (ReadMatchStmt (CanonSelector, Either a b))
  where
  type
    Selects
      (ReadMatchStmt (CanonSelector, Either a b))
    = Either Self
        (ReadMatchPun
          (CanonPath_
            (Either Self (NAString Void))
            (NAString Void)))
  type
    Key (ReadMatchStmt (CanonSelector, Either a b))
      = IDENTIFIER
  p #. k = punMatch (p #. k)

instance
  Assign_
    (ReadMatchStmt (CanonSelector, Either a b)) where
  type
    Lhs (ReadMatchStmt (CanonSelector, Either a b))
    = ReadContext CanonSelector ReadSelector
  type
    Rhs (ReadMatchStmt (CanonSelector, Either a b)) 
    = b
  ReadContext p (ReadSelector f) #= b
    = ReadMatchStmt
        (Inside (f (Leaf (p, Right b))))

{-
Selector
--------

A selector is interpreted as a function for injecting a sub-match into a larger match.
-}

newtype ReadSelector
  = ReadSelector
  { readSelector
     :: forall a
      . Paths (Map Text) a -> Assocs a
  }

proofSelector :: SELECTOR -> ReadSelector
proofSelector = parseSelector

instance IsString ReadSelector where
  fromString s
    = ReadSelector
        (wrapAssocs
          . Map.singleton (fromString s))

instance Select_ ReadSelector where
  type Selects ReadSelector
    = Either Self ReadSelector
  type Key ReadSelector = IDENTIFIER
  Left Self #. k
    = ReadSelector
        (wrapAssocs
          . Map.singleton (parseIdentifier k))
  
  Right (ReadSelector f) #. k
    = ReadSelector
        (f
          . wrapPaths
          . Map.singleton (parseIdentifier k))

{-
Path
----

A path is interpreted as a function for injecting a sub-declaration into a larger declaration.
-}

newtype ReadPath
  = ReadPath
  { readPath
     :: forall a . Paths (Map Text) a -> Assocs a
  }

pathProof :: PATH -> ReadPath
pathProof = parsePath

instance IsString ReadPath where
  fromString s
    = ReadPath
        (wrapAssocs 
          . Map.singleton (fromString s))

instance Select_ ReadPath where
  type Selects ReadPath = Either Self ReadPath
  type Key ReadPath = IDENTIFIER
  Left Self #. k
    = ReadPath
        (wrapAssocs
          . Map.singleton (parseIdentifier k))
  
  Right (ReadPath f) #. k
    = ReadPath
        (f
          . wrapPaths
          . Map.singleton (parseIdentifier k))

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

