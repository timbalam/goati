{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleContexts, FlexibleInstances, LambdaCase, DeriveFunctor #-}
module Goat.Repr.Lang.Expr
 where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( Self(..), notSelf, IDENTIFIER, parseIdentifier
  , BLOCK, parseBlock
  , STMT, parseStmt
  , DEFINITION, parseDefinition
  , PATTERN, parsePattern
  , PATH, parsePath
  )
import Goat.Repr.Pattern
  ( Public(..), Local(..), Matches
  , Declares, Components, Decompose
  , Bindings, Block, Ident, MonadBlock(..), Abs
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Expr
  ( Repr(..), emptyRepr, Expr(..)
  , Import(..), VarName, absFromBindings
  , (>>>=)
  )
import Goat.Util ((<&>), (...))
import Data.Bitraversable (bitraverse)
import Data.Function (on)
import qualified Data.Text as Text

-- Block

newtype ReadBlock a =
  ReadBlock {
    readBlock :: Bindings Declares Decompose (Repr Components) a
    }

proofBlock :: BLOCK a -> ReadBlock (Either (Esc ReadExpr) a)
proofBlock = parseBlock id

instance IsList (ReadBlock a) where
  type Item (ReadBlock a) = ReadStmt a
  fromList bdy = ReadBlock (foldMap readStmt bdy)
  toList =
    error "IsList (ReadPunBlock (Either Self ReadExpr) a): toList"

{- 
Stmt
----

We represent a *statement* as a set of declared bindings of values.
A *pun statement* generates an _escaped_ path and a corresponding binding selector.
-}

data Esc a = Escape a | Contain a deriving Functor

newtype ReadStmt a =
  ReadStmt {
    readStmt
     :: Bindings Declares Decompose (Repr Components) a
    }

proofStmt :: STMT a -> ReadStmt (Either (Esc ReadExpr) a)
proofStmt = parseStmt id

data ReadPun a = ReadPun a (ReadPathPun a)

punStmt :: ReadPun a -> ReadStmt (Either (Esc a) b)
punStmt (ReadPun a p) = case pathPunStmt p of
  ReadPatternPun (ReadStmt bs) (ReadPattern f) ->
    ReadStmt (f (Left (Escape a)) `mappend` bs)

instance IsString (ReadPun ReadExpr) where
  fromString s =
    ReadPun (fromString "" #. fromString s) (fromString s)

instance IsString (ReadStmt (Either (Esc ReadExpr) a)) where
  fromString s = punStmt (fromString s)

instance Select_ (ReadPun ReadExpr) where
  type Selects (ReadPun ReadExpr) =
    Either Self (ReadPun ReadExpr)
  type Key (ReadPun ReadExpr) = IDENTIFIER
  Left Self #. k = ReadPun (Left Self #. k) (Left Self #. k)
  Right (ReadPun a b) #. k =
    ReadPun (Right a #. k) (Right b #. k)

instance Select_ (ReadStmt (Either (Esc ReadExpr) a)) where
  type Selects (ReadStmt (Either (Esc ReadExpr) a)) =
    Either Self (ReadPun ReadExpr)
  type Key (ReadStmt (Either (Esc ReadExpr) a)) = IDENTIFIER
  r #. k = punStmt (r #. k)

instance Assign_ (ReadStmt (Either (Esc a) b)) where
  type Lhs (ReadStmt (Either (Esc a) b)) =
    ReadPatternPun (Esc a) b
  type Rhs (ReadStmt (Either (Esc a) b)) = b
  ReadPatternPun (ReadStmt bs) (ReadPattern f) #= b =
    ReadStmt (f (Right b) `mappend` bs)


-- Generate a local pun for each bound public path.

data ReadPathPun a =
  ReadPublic a ReadPath ReadPath | ReadLocal ReadPath

proofPath :: PATH -> ReadPathPun ReadExpr
proofPath = parsePath

data ReadPatternPun a b =
  ReadPatternPun (ReadStmt (Either a b)) ReadPattern

proofPattern
 :: PATTERN -> ReadPatternPun (Esc ReadExpr) a
proofPattern = parsePattern

pathPunStmt :: ReadPathPun a -> ReadPatternPun (Esc a) b
pathPunStmt (ReadLocal p) =
  ReadPatternPun (ReadStmt mempty) (setPattern p)
pathPunStmt (ReadPublic a lp pp) =
  ReadPatternPun
    (ReadStmt (readPattern (setPattern lp) (Left (Contain a))))
    (setPattern pp)

instance IsString (ReadPathPun a) where
  fromString s = ReadLocal (fromString s) 

instance IsString (ReadPatternPun (Esc a) b) where
  fromString s = pathPunStmt (fromString s)

instance Select_ (ReadPathPun ReadExpr) where
  type Selects (ReadPathPun ReadExpr) =
    Either Self (ReadPathPun ReadExpr)
  type Key (ReadPathPun ReadExpr) = IDENTIFIER
  Left Self #. k =
    ReadPublic (Left Self #. k) (parseIdentifier k)
      (Left Self #. k)
  
  Right (ReadLocal p) #. k = ReadLocal (Right p #. k)
  Right (ReadPublic p l a) #. k =
    ReadPublic (Right p #. k) (Right l #. k) (Right a #. k)

instance Select_ (ReadPatternPun (Esc ReadExpr) b) where
  type Selects (ReadPatternPun (Esc ReadExpr) b) =
    Either Self (ReadPathPun ReadExpr)
  type Key (ReadPatternPun (Esc ReadExpr) b) = IDENTIFIER
  p #. k = pathPunStmt (p #. k)

instance IsList (ReadPatternPun a b) where
  type Item (ReadPatternPun a b) =
    ReadMatchStmt
      (Either (ReadPatternPun a b) (ReadPatternPun a b))
  fromList ms = ReadPatternPun (ReadStmt bs) (fromList ms')
    where
      (bs, ms') =
        traverse
          (\ (ReadMatchStmt m) ->
            ReadMatchStmt <$>
              traverse (bitraverse punToPair punToPair) m)
          ms
      
      punToPair (ReadPatternPun (ReadStmt bs) p) = (bs, p)
  
  toList = error "IsList (ReadPatternPun a): toList"

instance Extend_ (ReadPatternPun a b) where
  type Extension (ReadPatternPun a b) =
    ReadPatternBlock
      (Either (ReadPatternPun a b) (ReadPatternPun a b))
  ReadPatternPun (ReadStmt bs) p # ReadPatternBlock m =
    ReadPatternPun
      (ReadStmt (bs `mappend` bs'))
      (p # ReadPatternBlock m')
    where
      (bs', m') = traverse (bitraverse punToPair punToPair) m
      
      punToPair (ReadPatternPun (ReadStmt bs) p) = (bs, p)

{-
Definition
----------

We represent an _escaped_ definiton as a definition nested inside a variable.
-}

newtype ReadExpr =
  ReadExpr {
    readExpr
     :: Repr Components (VarName Ident Ident (Import Ident))
    }

proofDefinition :: DEFINITION -> Either Self ReadExpr
proofDefinition = parseDefinition

getDefinition
 :: Either Self ReadExpr
 -> Repr Components (VarName Ident Ident (Import Ident))
getDefinition m = readExpr (notSelf m)

definition
 :: Repr Components (VarName Ident Ident (Import Ident))
 -> Either Self ReadExpr
definition m = pure (ReadExpr m)

escapeExpr
 :: Monad m
 => Esc (m (VarName a b c))
 -> m (VarName a b (m (VarName a b c)))
escapeExpr (Escape m) = return (Right (Right m))
escapeExpr (Contain m) =
  m <&> fmap (fmap (return . Right . Right))

joinExpr
 :: Monad m
 => m (VarName a b (m (VarName a b c)))
 -> m (VarName a b c)
joinExpr m = m >>= \case
  Left l -> return (Left l)
  Right (Left p) -> return (Right (Left p))
  Right (Right m) -> m

instance Num (Either Self ReadExpr) where
  fromInteger d = definition (Repr (Number (fromInteger d)))
  (+) = error "Num (Either Self ReadExpr): (+)"
  (*) = error "Num (Either Self ReadExpr): (*)"
  abs = error "Num (Either Self ReadExpr): abs"
  signum = error "Num (Either Self ReadExpr): signum"
  negate = error "Num (Either Self ReadExpr): negate"
  
instance Fractional (Either Self ReadExpr) where
  fromRational r =  definition (Repr (Number (fromRational r)))
  (/) = error "Fractional (Either Self ReadExpr): (/)"

instance TextLiteral_ (Either Self ReadExpr) where
  quote_ s = definition (Repr (Text (Text.pack s)))

readBinop
 :: (forall f m x . m x -> m x -> Expr f m x)
 -> Either Self ReadExpr
 -> Either Self ReadExpr
 -> Either Self ReadExpr
readBinop op m n = definition (Repr (on op getDefinition m n))

readUnop
 :: (forall f m x . m x -> Expr f m x)
 -> Either Self ReadExpr -> Either Self ReadExpr
readUnop op m = definition (Repr (op (getDefinition m)))

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
  use_ k =
    definition (Var (Right (Right (Import (parseIdentifier k)))))

instance IsString ReadExpr where
  fromString s =
    ReadExpr (Var (Right (Left (Local (fromString s)))))

instance Select_ ReadExpr where
  type Selects ReadExpr = Either Self ReadExpr
  type Key ReadExpr = IDENTIFIER
  Left Self #. k =
    ReadExpr (Var (Left (Public (parseIdentifier k))))
  Right (ReadExpr m) #. k =
    ReadExpr (Repr (Sel m (parseIdentifier k)))

instance IsList (Either Self ReadExpr) where
  type Item (Either Self ReadExpr) =
    ReadStmt (Either (Esc ReadExpr) (Either Self ReadExpr))
  fromList bdy =
    definition
      (joinExpr (wrapBlock (absFromBindings bs' emptyRepr)))
    where
      bs' = readBlock (fromList bdy) >>>= escapeExpr . 
        either (fmap readExpr) (Contain . getDefinition)
        
      
  toList = error "IsList (Either Self ReadExpr): toList"

instance Extend_ (Either Self ReadExpr) where
  type Extension (Either Self ReadExpr) =
    ReadBlock (Either (Esc ReadExpr) (Either Self ReadExpr))
  a # ReadBlock bs =
    definition (joinExpr (wrapBlock (absFromBindings bs' a')))
    where
      bs' =
        bs >>>=
        escapeExpr . 
          either (fmap readExpr) (Contain . getDefinition)
      a' = escapeExpr (Escape (getDefinition a))
