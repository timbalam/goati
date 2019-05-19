{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleContexts, FlexibleInstances, LambdaCase #-}
module Goat.Repr.Lang.Expr
 where

import Goat.Lang.Class
import Goat.Lang.Parser
  ( Self(..), notSelf, IDENTIFIER, parseIdentifier
  , BLOCK, parseBlock
  , STMT, parseStmt
  , DEFINITION, parseDefinition
  )
import Goat.Repr.Pattern
  ( Public(..), Local(..)
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
import Data.Function (on)
import qualified Data.Text as Text

-- Block

newtype ReadBlock a =
  ReadBlock {
    readBlock
     :: Bindings
          Declares Decompose (Repr Components) (Esc a)
    }

instance IsList (ReadBlock a) where
  type Item (ReadBlock a) = ReadStmt a
  fromList bdy = ReadBlock (foldMap readStmt bdy)
  toList = error "IsList (ReadBlock a): toList"

proofBlock
 :: BLOCK DEFINITION -> ReadBlock (Either Self ReadExpr)
proofBlock = parseBlock parseDefinition


{- 
Stmt
----

We represent a *statement* as a set of declared bindings of values.
A *pun statement* generates an _escaped_ path and a corresponding binding selector.
-}

newtype ReadStmt a =
  ReadStmt {
    readStmt
     :: Bindings Declares Decompose (Repr Components) (Esc a)
    }

proofStmt
 :: STMT DEFINITION -> ReadStmt (Either Self ReadExpr)
proofStmt = parseStmt parseDefinition

data ReadPun p a = ReadPun (ReadPathPun p a) a

data Esc a = Escape a | Contain a

punStmt :: ReadPun ReadPath a -> ReadStmt a
punStmt (ReadPun p a) = case pathPunStmt p of
  ReadPatternPun (ReadPattern f) (ReadBlock bs) ->
    ReadStmt (f (Escape a) `mappend` bs)

instance IsString (ReadPun ReadPath (Either Self ReadExpr)) where
  fromString s =
    ReadPun (fromString "" #. fromString s) (fromString s)

instance IsString (ReadStmt (Either Self ReadExpr)) where
  fromString s = punStmt (fromString s)

instance Select_ (ReadPun ReadPath (Either Self ReadExpr)) where
  type Selects (ReadPun ReadPath (Either Self ReadExpr)) =
    Either Self (ReadPun ReadPath ReadExpr)
  type Key (ReadPun ReadPath (Either Self ReadExpr)) =
    IDENTIFIER
  Left Self #. k = ReadPun (Left Self #. k) (Left Self #. k)
  Right (ReadPun r a) #. k =
    ReadPun (Right r #. k) (Right a #. k)

instance Select_ (ReadStmt (Either Self ReadExpr)) where
  type Selects (ReadStmt (Either Self ReadExpr)) =
    Either Self (ReadPun ReadPath ReadExpr)
  type Key (ReadStmt (Either Self ReadExpr)) = IDENTIFIER
  r #. k = punStmt (r #. k)

instance Assign_ (ReadStmt a) where
  type Lhs (ReadStmt a) = ReadPatternPun ReadPattern a
  type Rhs (ReadStmt a) = a
  ReadPatternPun (ReadPattern f) (ReadBlock bs) #= a =
    ReadStmt (f (Contain a) `mappend` bs)


-- Generate a local pun for each bound public path.

data ReadPathPun p a = ReadPublic p p a | ReadLocal p
data ReadPatternPun p a = ReadPatternPun p (ReadBlock a)

pathPunStmt
 :: ReadPathPun ReadPath a
 -> ReadPatternPun ReadPattern a
pathPunStmt (ReadLocal p) =
  ReadPatternPun (setPattern p) (ReadBlock mempty)
pathPunStmt (ReadPublic pp lp a) =
  ReadPatternPun
    (setPattern pp)
    (ReadBlock (readPattern (setPattern lp) (Contain a)))

instance IsString (ReadPathPun ReadPath a) where
  fromString s = ReadLocal (fromString s) 

instance IsString (ReadPatternPun ReadPattern a) where
  fromString s = pathPunStmt (fromString s)

instance
  Select_ (ReadPathPun ReadPath (Either Self ReadExpr))
  where
    type Selects (ReadPathPun ReadPath (Either Self ReadExpr)) =
      Either Self (ReadPathPun ReadPath ReadExpr)
    type Key (ReadPathPun ReadPath (Either Self ReadExpr)) =
      IDENTIFIER
    Left Self #. k =
      ReadPublic (Left Self #. k) (parseIdentifier k)
        (Left Self #. k)
    
    Right (ReadLocal p) #. k = ReadLocal (Right p #. k)
    Right (ReadPublic p l a) #. k =
      ReadPublic (Right p #. k) (Right l #. k) (Right a #. k)

instance
  Select_ (ReadPatternPun ReadPattern (Either Self ReadExpr))
  where
    type
      Selects
        (ReadPatternPun ReadPattern (Either Self ReadExpr)) =
        Either Self (ReadPathPun ReadPath ReadExpr)
    type
      Key (ReadPatternPun ReadPattern (Either Self ReadExpr)) =
        IDENTIFIER
    p #. k = pathPunStmt (p #. k)

instance IsList (ReadPatternPun ReadPattern a) where
  type Item (ReadPatternPun ReadPattern a) =
    ReadMatchStmt (ReadPatternPun ReadPattern a)
  fromList ms = ReadPatternPun (fromList ms') (ReadBlock bs)
    where
      (bs, ms') =
        traverse
          (\ (ReadMatchStmt m) ->
            ReadMatchStmt <$>
              traverse
                (\ (ReadPatternPun p (ReadBlock bs)) -> (bs, p))
                m)
          ms
  toList = error "IsList (ReadPatternPun ReadPattern a): toList"

instance Extend_ (ReadPatternPun ReadPattern a) where
  type Extension (ReadPatternPun ReadPattern a) =
    ReadPatternBlock (ReadPatternPun ReadPattern a)
  ReadPatternPun p (ReadBlock bs) # ReadPatternBlock m =
    ReadPatternPun
      (p # ReadPatternBlock m')
      (ReadBlock (bs `mappend` bs'))
    where
      (bs', m') =
        traverse
          (\ (ReadPatternPun p (ReadBlock bs)) -> (bs, p))
          m


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

instance IsString (Either Self ReadExpr) where
  fromString s =
    definition (Var (Right (Left (Local (fromString s)))))

instance Select_ ReadExpr where
  type Selects ReadExpr = Either Self ReadExpr
  type Key ReadExpr = IDENTIFIER
  Left Self #. k =
    ReadExpr (Var (Left (Public (parseIdentifier k))))
  Right (ReadExpr m) #. k =
    ReadExpr (Repr (Sel m (parseIdentifier k)))

instance IsList (Either Self ReadExpr) where
  type Item (Either Self ReadExpr) =
    ReadStmt (Either Self ReadExpr)
  fromList bdy =
    definition
      (joinExpr
        (wrapBlock 
          (absFromBindings
            (readBlock (fromList bdy) >>>=
              escapeExpr . fmap getDefinition)
            emptyRepr)))
  toList = error "IsList (Either Self ReadExpr): toList"

instance Extend_ (Either Self ReadExpr) where
  type Extension (Either Self ReadExpr) =
    ReadBlock (Either Self ReadExpr)
  a # ReadBlock b =
    definition
      (joinExpr
        (wrapBlock
          (absFromBindings
            (b >>>= escapeExpr . fmap getDefinition)
            (escapeExpr (Escape (getDefinition a))))))
