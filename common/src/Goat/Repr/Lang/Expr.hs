{-# LANGUAGE RankNTypes, TypeFamilies, FlexibleContexts, FlexibleInstances, LambdaCase #-}
module Goat.Repr.Lang.Expr
 where

import Goat.Lang.Class
import Goat.Lang.Parser (Self(..), IDENTIFIER, parseIdentifier)
import Goat.Repr.Pattern
  ( Public(..), Local(..)
  , Declares, Components, Decompose
  , Bindings, Block, Ident, MonadBlock, Abs
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Expr
  ( Repr(..), emptyRepr, Expr(..)
  , Import(..), VarName, reprFromBindings
  , (>>>=)
  )
import Goat.Util ((<&>))
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


{- 
Stmt
----

We represent a *statement* as a set of declared bindings of values.
A *pun statement* generates an _escaped_ path and a corresponding binding selector.
-}

newtype ReadStmt a =
  ReadStmt {
    readStmt
     :: Bindings
          Declares Decompose (Repr Components) (Esc a)
    }

data ReadPun p a = ReadPun p a

data Esc a = Escape a | Contain a

punStmt :: ReadPun (ReadPathPun ReadPath a) a -> ReadStmt a
punStmt (ReadPun p a) = case pathPunStmt p of
  ReadPatternPun (ReadPattern f) (ReadBlock bs) ->
    ReadStmt (f (Escape a) `mappend` bs)

instance
  IsString (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr)
  where
    fromString s =
      ReadPun (fromString "" #. fromString s) (fromString s)

instance IsString (ReadStmt ReadExpr) where
  fromString s = punStmt (fromString s)

instance
  Select_ (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr) where
  type Selects
    (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr) =
    Either Self
      (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr)
  type Key (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr) =
    IDENTIFIER
  Left Self #. k = ReadPun (Left Self #. k) (Left Self #. k)
  Right (ReadPun r a) #. k = ReadPun (Right r #. k) (Right a #. k)

instance Select_ (ReadStmt ReadExpr) where
  type Selects (ReadStmt ReadExpr) =
    Either Self
      (ReadPun (ReadPathPun ReadPath ReadExpr) ReadExpr)
  type Key (ReadStmt ReadExpr) = IDENTIFIER
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
  Select_ (ReadPathPun ReadPath ReadExpr) where
  type Selects (ReadPathPun ReadPath ReadExpr) =
    Either Self (ReadPathPun ReadPath ReadExpr)
  type Key (ReadPathPun ReadPath ReadExpr) = IDENTIFIER
  Left Self #. k =
    ReadPublic
      (Left Self #. k)
      (parseIdentifier k)
      (Left Self #. k)
  
  Right (ReadLocal p) #. k = ReadLocal (Right p #. k)
  Right (ReadPublic p l a) #. k =
    ReadPublic (Right p #. k) (Right l #. k) (Right a #. k)

instance
  Select_ (ReadPatternPun ReadPattern ReadExpr) where
  type Selects (ReadPatternPun ReadPattern ReadExpr) =
    Either Self (ReadPathPun ReadPath ReadExpr)
  type Key (ReadPatternPun ReadPattern ReadExpr) = IDENTIFIER
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

escapeExpr
 :: Esc ReadExpr
 -> Repr Components (VarName Ident Ident ReadExpr)
escapeExpr (Escape e) = return (Right (Right e))
escapeExpr (Contain (ReadExpr m)) = m <&> \case
  Left l         -> Left l
  Right (Left p) -> Right (Left p)
  Right (Right i) ->
    Right (Right (ReadExpr (return (Right (Right i)))))

joinExpr
 :: Repr Components (VarName Ident Ident ReadExpr)
 -> ReadExpr
joinExpr m = ReadExpr (m >>= \case
  Left l -> return (Left l)
  Right (Left p) -> return (Right (Left p))
  Right (Right (ReadExpr m)) -> m)

instance Num ReadExpr where
  fromInteger d = ReadExpr (Repr (Number (fromInteger d)))
  (+) = error "Num ReadExpr: (+)"
  (*) = error "Num ReadExpr: (*)"
  abs = error "Num ReadExpr: abs"
  signum = error "Num ReadExpr: signum"
  negate = error "Num ReadExpr: negate"
  
instance Fractional ReadExpr where
  fromRational r = ReadExpr (Repr (Number (fromRational r)))
  (/) = error "Fractional ReadExpr: (/)"

instance TextLiteral_ ReadExpr where
  quote_ s = ReadExpr (Repr (Text (Text.pack s)))

readBinop
 :: (forall f m x . m x -> m x -> Expr f m x)
 -> ReadExpr -> ReadExpr -> ReadExpr
readBinop op (ReadExpr m) (ReadExpr n) =
  ReadExpr (Repr (m `op` n))

readUnop
 :: (forall f m x . m x -> Expr f m x)
 -> ReadExpr -> ReadExpr
readUnop op (ReadExpr m) = ReadExpr (Repr (op m))
      
instance Operator_ ReadExpr where
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
  
instance Use_ ReadExpr where
  type Extern ReadExpr = IDENTIFIER
  use_ k =
    ReadExpr (Var (Right (Right (Import (parseIdentifier k)))))

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

instance IsList ReadExpr where
  type Item ReadExpr = ReadStmt ReadExpr
  fromList bdy =
    joinExpr
      (reprFromBindings
        (readBlock (fromList bdy) >>>= escapeExpr)
        emptyRepr)
  toList = error "IsList ReadExpr: toList"

instance Extend_ ReadExpr where
  type Extension ReadExpr = ReadBlock ReadExpr
  a # ReadBlock b =
    joinExpr
      (reprFromBindings
        (b >>>= escapeExpr)
        (escapeExpr (Escape a)))
