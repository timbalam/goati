{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleContexts, FlexibleInstances, LambdaCase, DeriveFunctor #-}
module Goat.Repr.Lang.Expr
  ( module Goat.Repr.Lang.Expr
  , Self
  )
where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( Self(..), notSelf
  , IDENTIFIER, parseIdentifier
  , BLOCK, parseBlock
  , STMT, parseStmt
  , DEFINITION, parseDefinition
  , PATTERN, parsePattern
  , PATH, parsePath
  --, CanonPath, CanonPath_, CanonSelector
  )
import Goat.Repr.Pattern
import Goat.Repr.Lang.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>), (...))
import Data.Bifunctor (first, bimap)
import Data.Bifoldable (bifoldMap)
import Data.Bitraversable (bitraverse)
import Data.Coerce (coerce)
import Data.Function (on)
import Data.Monoid (Endo(..))
import qualified Data.Text as Text
import Bound ((>>>=))

-- Block

type Matched = (,,) [Trail Ident]
type Declared = (,,) [ViewTrails Ident]
type Imported = (,,) [Ident]

newtype ReadBlock a
  = ReadBlock
  { readBlock
     :: Bindings
          (ViewCpts (Trail Ident))
          (Assocs' Matched Ident)
          (Repr
            (Defns
              Declared Matched (Assocs' Imported))
            ())
          a
  }

proofBlock
 :: BLOCK a -> ReadBlock (Either (Esc ReadExpr) a)
proofBlock = parseBlock id

instance IsList (ReadBlock a) where
  type Item (ReadBlock a) = ReadStmt a
  fromList bdy = ReadBlock (foldMap readStmt bdy)
  toList
    = error
        "IsList (ReadPunBlock (Either Self ReadExpr) a): toList"

{- 
Stmt
----

We represent a *statement* as a set of declared bindings of values.
A *pun statement* generates an _escaped_ path and a corresponding binding selector.
-}

data Esc a = Escape a | Contain a deriving Functor

newtype ReadStmt a
  = ReadStmt
  { readStmt
     :: Bindings
          (ViewCpts [Trail Ident])
          (Assocs' Matched)
          (Repr
            (Defns
              Declared Matched (Assocs' Imported))
            ())
          a
  }

proofStmt
 :: STMT a -> ReadStmt (Either (Esc ReadExpr) a)
proofStmt = parseStmt id

data ReadPun a
  = ReadPun
      (forall x . Selector_ x => x)
      (ReadPathPun a)

proofPun :: PATH -> ReadPun CanonPath
proofPun = parsePath

punStmt
 :: Selector_ a
 => ReadPun CanonPath -> ReadStmt (Either (Esc a) b)
punStmt (ReadPun a p)
  = case pathPunStmt p of
    ReadPatternWithShadowStmts
      (ReadStmt f) (ReadPattern g)
     -> ReadStmt
          (\ an
           -> g an id (Left (Escape a))
           `mappend` f an)

instance
  (IsString a, IsString b)
   => IsString (ReadPun (CanonPath_ a b)) where
  fromString s
    = ReadPun
        (fromString "" #. fromString s)
        (fromString s)

instance IsString a => IsString (Esc a) where
  fromString s = Contain (fromString s)

instance
  Selector_ a
   => IsString (ReadStmt (Either (Esc a) b))
  where
  fromString s = punStmt (fromString s)

instance
  (IsString a, IsString b)
   => Select_ (ReadPun (CanonPath_ a b)) where
  type Selects (ReadPun (CanonPath_ a b))
    = Either Self
        (ReadPun (CanonPath_ (Either Self b) b))
  type Key (ReadPun (CanonPath_ a b)) = IDENTIFIER
  Left Self #. k
    = ReadPun
        (fromString "" #. parseIdentifier k)
        (Left Self #. k)

  Right (ReadPun a b) #. k
    = ReadPun (a #. parseIdentifier k) (Right b #. k)

instance Select_ a => Select_ (Esc a) where
  type Selects (Esc a) = Selects a
  type Key (Esc a) = Key a
  a #. k = Contain (a #. k)

instance
  Selector_ a
   => Select_ (ReadStmt (Either (Esc a) b))
  where
  type Selects (ReadStmt (Either (Esc a) b))
    = Either Self
        (ReadPun
          (CanonPath_
            (Either Self IDENTIFIER) IDENTIFIER))
  type Key (ReadStmt (Either (Esc a) b))
    = IDENTIFIER
  r #. k = punStmt (r #. k)

instance
  Selector_ a => Assign_ (ReadStmt (Either a b)) 
  where
  type Lhs (ReadStmt (Either a b))
    = ReadPatternPun a b
  type Rhs (ReadStmt (Either a b)) = b
  ReadPatternWithShadowStmts
    (ReadStmt f) (ReadPattern g)
   #= b
    = ReadStmt
        (\ an
         -> g an id (Right b) `mappend` f an)


-- Generate a local pun for each bound public path.

data ReadPathPun a
  = ReadPublicWithLocalShadow
      (forall x . Selector_ x => x)
      -- ^ local shadow value
      ReadPath -- ^ local shadow path
      (ReadContext a ReadPath) -- ^ public path
  | ReadLocal (ReadContext a ReadPath)

proofPath :: PATH -> ReadPathPun CanonPath
proofPath = parsePath

data ReadPatternPun a b
  = ReadPatternWithShadowStmts
      (ReadStmt (Either a b))
      ReadPattern

proofPattern
 :: Selector_ a => PATTERN -> ReadPatternPun a b
proofPattern = parsePattern

pathPunStmt
 :: Selector_ a
 => ReadPathPun CanonPath -> ReadPatternPun a b
pathPunStmt (ReadLocal p)
  = ReadPatternWithShadowStmts
      (ReadStmt mempty) (setPatternWithContext p)

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

instance
  IsString a => IsString (ReadPathPun a) where
  fromString s = ReadLocal (fromString s) 

instance IsString (ReadPatternPun a b) where
  fromString s
    = ReadPatternWithShadowStmts
        (ReadStmt mempty) (fromString s)

instance
  (IsString a, IsString b)
   => Select_ (ReadPathPun (CanonPath_ a b)) where
  type Selects (ReadPathPun (CanonPath_ a b))
    = Either
        Self
        (ReadPathPun (CanonPath_ (Either Self b) b))
  type Key (ReadPathPun (CanonPath_ a b))
    = IDENTIFIER
  Left Self #. k
    = ReadPublicWithLocalShadow
        (fromString "" #. parseIdentifier k)
        (parseIdentifier k)
        (fromString "" #. k)
  
  Right (ReadLocal (ReadContext pa pb)) #. k
    = ReadLocal (ReadContext pa (Right pb) #. k)
  Right
    (ReadPublicWithLocalShadow
      a l (ReadContext pa pb))
    #. k
    = ReadPublicWithLocalShadow
        (a #. parseIdentifier k)
        (Right l #. k)
        (ReadContext pa (Right pb) #. k)

instance
  Selector_ a => Select_ (ReadPatternPun a b)
  where
  type Selects (ReadPatternPun a b)
    = Either Self
        (ReadPathPun
          (CanonPath_
            (Either Self IDENTIFIER) IDENTIFIER))
  type Key (ReadPatternPun a b) = IDENTIFIER
  p #. k = pathPunStmt (p #. k)


instance
  Selector_ a => IsList (ReadPatternPun a b)
  where
  type Item (ReadPatternPun a b)
    = ReadMatchStmt
        (Either
          (ReadPatternPun a b)
          (ReadPatternPun a b))
  fromList ms
    = ReadPatternWithShadowStmts s (fromList ms')
    where
    s = ReadStmt
          (foldMap
            (foldMap 
              (bifoldMap
                readShadowStmts
                readShadowStmts)
              . (`readMatchStmt` id))
            ms)
      where
      readShadowStmts
        (ReadPatternWithShadowStmts (ReadStmt f) _) 
        = f
    
    ms'
      = map
          (\ (ReadMatchStmt f)
           -> ReadMatchStmt
                (fmap
                  (bimap
                    getPattern getPattern)
                  . f))
          ms
      where
        getPattern (ReadPatternWithShadowStmts _ p)
          = p
  
  toList = error "IsList (ReadPatternPun a): toList"

instance
  Selector_ a => Extend_ (ReadPatternPun a b)
  where
  type Extension (ReadPatternPun a b)
    = ReadPatternBlock
        (Either
          (ReadPatternPun a b)
          (ReadPatternPun a b))
          
  ReadPatternWithShadowStmts s p
    # ReadPatternBlock g
    = ReadPatternWithShadowStmts
        (ReadStmt (readStmt s' `mappend` readStmt s))
        (p # ReadPatternBlock g')
    where
    g' 
     :: (Int -> CanonSelector -> t)
     -> Matches
          (Ambig
            ((,) t)
            (Either ReadPattern ReadPattern))
    g' an
      = fmap (bimap getPattern getPattern)
     <$> g an
      where
      getPattern (ReadPatternWithShadowStmts _ p)
        = p
    
    s'
      = ReadStmt
          (foldMap 
            (foldMap
              (either
                readShadowStmts
                readShadowStmts))
            (g (,)))
      where
       readShadowStmts
        (ReadPatternWithShadowStmts (ReadStmt f) _)
        = f

{-
Definition
----------

We represent an _escaped_ definiton as a definition nested inside a variable.
-}

newtype ReadExpr
  = ReadExpr
  { readExpr
     :: Repr
          (TagCpts Declared Matched (Cpts Imported))
          ()
          (VarName Ident Ident (Import Ident))
  }

proofDefinition :: DEFINITION -> Either Self ReadExpr
proofDefinition = parseDefinition

getDefinition
 :: Either Self ReadExpr
 -> Repr
      (TagCpts Declared Matched (Cpts Imported))
      ()
      (VarName Ident Ident (Import Ident))
getDefinition m = readExpr (notSelf m)

definition
 :: (forall h
      . Repr
          (TagCpts Declared Matched (Cpts Imported))
          ()
          (VarName Ident Ident (Import Ident)))
 -> Either Self ReadExpr
definition m = pure (ReadExpr m)

escapeExpr
 :: Monad m
 => Esc (m (VarName a b c))
 -> m (VarName a b (m (VarName a b c)))
escapeExpr (Escape m) = return (Right (Right m))
escapeExpr (Contain m)
  = m <&> fmap (fmap (return . Right . Right))

joinExpr
 :: Monad m
 => m (VarName a b (m (VarName a b c)))
 -> m (VarName a b c)
joinExpr m
  = m
 >>= \case
    Left l -> return (Left l)
    Right (Left p) -> return (Right (Left p))
    Right (Right m) -> m

newtype ReadValue
  = ReadValue { readValue :: forall a . Value a }

instance Num (Either Self ReadExpr) where
  fromInteger d
    = pure (ReadExpr (Repr (Number (fromInteger d))))
  (+) = error "Num (Either Self ReadExpr): (+)"
  (*) = error "Num (Either Self ReadExpr): (*)"
  abs = error "Num (Either Self ReadExpr): abs"
  signum = error "Num (Either Self ReadExpr): signum"
  negate = error "Num (Either Self ReadExpr): negate"

instance Fractional (Either Self ReadExpr) where
  fromRational r
    = pure
        (ReadExpr (Repr (Number (fromRational r))))
  (/)
    = error "Fractional (Either Self ReadExpr): (/)"

instance TextLiteral_ (Either Self ReadExpr) where
  quote_ s
    = pure (ReadExpr (Repr (Text (Text.pack s))))

readBinop
 :: (forall f m x . m x -> m x -> Expr f m x)
 -> Either Self ReadExpr
 -> Either Self ReadExpr
 -> Either Self ReadExpr
readBinop op m n
  = definition
      (Repr (Comp (memo (on op getDefinition m n))))

readUnop
 :: (forall f m x . m x -> Expr f m x)
 -> Either Self ReadExpr -> Either Self ReadExpr
readUnop op m
  = definition
      (Repr (Comp (memo (op (getDefinition m)))))

instance Operator_ (Either Self ReadExpr) where
  (#+)  = readBinop Add
  (#-)  = readBinop Sub
  (#*)  = readBinop Mul
  (#/)  = readBinop Div
  (#^)  = readBinop Pow
  (#==) = readBinop Eq
  (#!=) = readBinop Ne
  (#<)  = readBinop Lt
  (#<=) = readBinop Le
  (#>)  = readBinop Gt
  (#>=) = readBinop Ge
  (#||) = readBinop Or
  (#&&) = readBinop And
  neg_  = readUnop Neg
  not_  = readUnop Not
  
instance Use_ (Either Self ReadExpr) where
  type Extern (Either Self ReadExpr) = IDENTIFIER
  use_ k
    = definition
        (Var
          (Right
            (Right (Import (parseIdentifier k)))))

instance IsString ReadExpr where
  fromString s
    = ReadExpr
        (Var (Right (Left (Local (fromString s)))))

instance Select_ ReadExpr where
  type Selects ReadExpr = Either Self ReadExpr
  type Key ReadExpr = IDENTIFIER
  Left Self #. k
    = ReadExpr
        (Var (Left (Public (parseIdentifier k))))
  
  Right (ReadExpr m) #. k
    = ReadExpr
        (Repr
          (Comp (memo (Sel m (parseIdentifier k)))))

instance IsList (Either Self ReadExpr) where
  type Item (Either Self ReadExpr)
    = ReadStmt
        (Either
          (Esc ReadExpr)
          (Either Self ReadExpr))
  fromList bdy
    = definition 
        (joinExpr
          (Repr
            (Comp (memo (Ext bs emptyRepr)))))
    where
    bs
      = abstractBindings
          (readBlock (fromList bdy)
           >>>= escapeExpr
            . either
                (fmap readExpr)
                (Contain . getDefinition))

  toList
    = error "IsList (Either Self ReadExpr): toList"

instance Extend_ (Either Self ReadExpr) where
  type Extension (Either Self ReadExpr)
    = ReadBlock
        (Either
          (Esc ReadExpr)
          (Either Self ReadExpr))
  a # ReadBlock bs
    = definition
        (joinExpr
          (Repr
            (Comp (memo (Ext bs' a')))))
    where
    bs'
      = abstractBindings
          (bs
           >>>= escapeExpr
            . either
                (fmap readExpr)
                (Contain . getDefinition))
    a' = escapeExpr (Escape (getDefinition a))
