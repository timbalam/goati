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

newtype ReadPattern
  = ReadPattern 
  { readPattern
     :: forall t u m a
      . MonadBlock (BlockCpts ((,) [t])) m
     => (ExprCtx CanonPath -> t)
     -> (ExprCtx CanonSelector -> u)
     -> a
     -> Bindings
          (Inside (Ambig ((,) [t])) Declares) 
          (Cpts ((,) [u]))
          m
          a
  }

patternProof
 :: PATTERN -> ReadPattern
patternProof = parsePattern

setPattern
 :: ReadContext CanonPath ReadPath
 -> ReadPattern
setPattern (ReadContext p (ReadPath f))
  = ReadPattern
      (\ fp _fs
       -> Define . Inside . f
       . leafWith (fp (PathCtx p)) . return)
  where
  leafWith e a = Leaf (Ambig (pure ([e], a)))

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
    = ReadMatchStmt (Either ReadPattern ReadPattern)
  fromList bdy
    = ReadPattern
        (\ fp fs a
         -> (ignoreRemaining
              (bindPartsFromMatches
                (readPatternBlockWithContext
                  (either readPattern readPattern)
                  (fromList bdy)
                  fp
                  fs)
                a)))

  toList = error "IsList ReadPattern: toList"

instance Extend_ ReadPattern where
  type Extension ReadPattern
    = ReadPatternBlock
        (Either ReadPattern ReadPattern)
  ReadPattern f # pb
    = ReadPattern
        (\ fp fs a
         -> bindRemaining (f fp fs)
              (bindPartsFromMatches
                (readPatternBlockWithContext
                  (either readPattern readPattern)
                  pb
                  (fp . ExtCtx)
                  (fs . ExtCtx))
                a))

readPatternBlockWithContext
 :: (a
     -> (ExprCtx CanonPath -> t)
     -> (ExprCtx CanonSelector -> u)
     -> b)
 -> ReadPatternBlock a
 -> (ExprCtx CanonPath -> t)
 -> (ExprCtx CanonSelector -> u)
 -> Matches (Ambig ((,) [u]) b)
readPatternBlockWithContext
  k (ReadPatternBlock f) fp fs
  = f (\ i s -> (i, PathCtx s))
 <&> (\ (Ambig ne)
      -> Ambig (addContext k fp fs <$> ne))
  where
  addContext
    :: (a
        -> (ExprCtx p -> t)
        -> (ExprCtx s -> u)
        -> b)
    -> (ExprCtx p -> t)
    -> (ExprCtx s -> u)
    -> ((Int, ExprCtx s), a)
    -> ([u], b)
  addContext k fp fs ((i, p), a)
    = ([fs' p], k a fp' fs')
    where
    fp' = fp . StmtCtx i
    fs' = fs . StmtCtx i

{-
Pattern block
-------------

A pattern block is read as a selector tree of nested patterns.
-}

newtype ReadPatternBlock a
  = ReadPatternBlock
  { readPatternBlock
     :: forall t
      . (Int -> CanonSelector -> t)
     -> Matches (Ambig ((,) t) a)
  }

proofPatternBlock
 :: PATTERNBLOCK a
 -> ReadPatternBlock (Either ReadPattern a)
proofPatternBlock = parsePatternBlock id

instance IsList (ReadPatternBlock a) where
  type Item (ReadPatternBlock a) = ReadMatchStmt a
  fromList bdy
    = ReadPatternBlock
        (\ f
         -> case foldStmts f bdy of
            Inside kv -> kv)
    where
    foldStmts f
      = foldMap id
          . mapWithIndex
            (\ i m -> readMatchStmt m (f i))
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
     :: forall t
      . (CanonSelector -> t)
     -> Inside (Ambig ((,) t)) Matches a
  }

proofMatchStmt
 :: MATCHSTMT a
 -> ReadMatchStmt (Either ReadPattern a)
proofMatchStmt = parseMatchStmt id

data ReadMatchPun a
  = ReadMatchPun
      (forall x. Path_ x => x)
      (ReadContext a ReadSelector)

proofMatchPun :: PATH -> ReadMatchPun CanonSelector
proofMatchPun = parsePath

punMatch
 :: Path_ a
 => ReadMatchPun CanonSelector
 -> ReadMatchStmt (Either a b)
punMatch
  (ReadMatchPun a (ReadContext p (ReadSelector f)))
  = ReadMatchStmt
      (Inside . f . leafWith  (Left a)
        . (`id` p))
  where
  leafWith a e = Leaf (Ambig (pure (e, a)))

instance
  IsString b
   => IsString (ReadMatchPun (CanonPath_ a b)) where
  fromString s
    = ReadMatchPun
        (fromString s)
        (fromString "" #. fromString s)

instance
  Path_ a => IsString (ReadMatchStmt (Either a b))
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
  Path_ a => Select_ (ReadMatchStmt (Either a b))
  where
  type Selects (ReadMatchStmt (Either a b))
    = Either Self
        (ReadMatchPun
          (CanonPath_
            (Either Self (NAString Void))
            (NAString Void)))
  type Key (ReadMatchStmt (Either a b)) = IDENTIFIER
  p #. k = punMatch (p #. k)

instance Assign_ (ReadMatchStmt (Either a b)) where
  type Lhs (ReadMatchStmt (Either a b))
    = ReadContext CanonSelector ReadSelector
  type Rhs (ReadMatchStmt (Either a b)) = b
  ReadContext p (ReadSelector f) #= b
    = ReadMatchStmt
        (Inside . f . leafWith (Right b)
          . (`id` p))
    where
    leafWith a e = Leaf (Ambig (pure (e, a)))

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
data ReadContext a b
  = ReadContext a b

instance
  (IsString a, IsString b)
   => IsString (ReadContext a b)
  where
  fromString s
    = ReadContext (fromString s) (fromString s)

instance
  (Select_ a, Select_ b)
   => Select_ (ReadContext a b)
  where
  type Selects (ReadContext a b)
    = ReadContext (Selects a) (Selects b)
  type Key (ReadContext a b) = IDENTIFIER
  ReadContext a b #. k
    = ReadContext
        (a #. parseIdentifier k)
        (b #. parseIdentifier k)
