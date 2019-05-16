{-# LANGUAGE RankNTypes, TypeFamilies #-}
module Goat.Repr.Lang.Expr
 where

import Goat.Lang.Class
import Goat.Repr.Pattern
  ( Public(..), Local(..)
  , Declares, Components
  , Bindings, Block
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Expr
  ( Repr(..), emptyRepr, Expr(..)
  , Extern(..), VarName, reprFromBindings
  )
import qualified Data.Text as Text

-- Block

newtype ReadBlock a =
  ReadBlock {
    readBlock ::
      forall m . Monad m => Bindings Declares (Components ()) m a
    }

instance IsList (ReadBlock a) where
  type Item ReadBlock = ReadStmt a
  fromList bdy =
    ReadBlock
      (ReadExpr .
        blockBindings (foldMap readDefn bdy) .
        readExpr)


{- 
Stmt
----

We represent a *statement* as a set of declared bindings of values.
A *pun statement* generates a value corresponding to a binding that _escapes_ to the parent environment.
-}

newtype ReadStmt a =
  ReadStmt {
    readDefn
     :: forall m . MonadBlock (Abs Components) m
     => Bindings Declares (Components ()) m (Esc a)
    }

punStmt :: ReadPun p a -> ReadStmt a
punStmt (ReadPun (ReadPattern f) a) = ReadStmt (f (Escape a))

data Esc a = Escape a | Unescaped a

instance IsString a => IsString (ReadPun ReadPattern a) where
  fromString s =
    ReadPun
      (fromString "" #. fromString s)
      (fromString s)

instance IsString (ReadStmt a) where
  fromString s = punStmt (fromString s)

instance Selects_ a => Select_ (ReadPun ReadPattern a) where
  type Selects (ReadPun ReadPattern a) =
    ReadPun (Either Self ReadPattern) (Selects a)
  type Key (ReadPun ReadPattern a) = IDENTIFIER
  ReadPun r a #. k = 
    ReadPun (r #. parseIdentifier k) (a #. parseIdentifier k)

instance Select_ a => Select_ (ReadStmt a) where
  type Selects (ReadStmt a) =
    Pun (Either Self ReadPattern) (Selects a)
  type Key (ReadStmt a) = IDENTIFIER
  r #. k = punStmt (r #. k)

instance Assign_ (ReadStmt a) where
  type Lhs (ReadStmt a) = ReadPattern
  type Rhs (ReadStmt a) = a
  ReadPattern f #= a = ReadStmt (f (Unescaped a))


-- Generate a local pun for each bound public path.

data ReadPathPun p a =
  ReadPublic p p a | ReadLocal p

instance IsString (ReadPathPun ReadPath a) where
  fromString s = ReadLocal (fromString s) 

instance
  (Select_ a, IsString (Compound a))
    => Select_ (ReadPathPun ReadPath a) where
  type Selects (ReadPathPun ReadPath a) =
    Either Self (ReadPathPun ReadPath (Selects a))
  type Key (ReadPathPun ReadPath) = IDENTIFIER
  Left Self #. k =
    ReadPublic
      (Left Self #. k)
      (parseIdentifier k)
      (fromString "" #. parseIdentifier k)
  
  Right (ReadLocal p) #. k = ReadLocal (p #. k)
  Right (ReadPublicPun p l a) #. k =
    ReadPublic (p #. k) (l #. k) (a #. parseIdentifier k)


{-
Definition
----------

-}


newtype ReadExpr =
  ReadExpr {
    readExpr
     :: Repr
          Components
          (VarName Ident Ident (Extern Ident))
    }

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

instance Text_ ReadExpr where
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
  
instance Extern_ ReadExpr where
  use_ n = ReadExpr (Var (Right (Right (Extern n))))

instance IsString ReadExpr where
  fromString n =
    ReadExpr (Var (Right (Left (Local (fromString n)))))

instance Select_ ReadExpr where
  type Selects ReadExpr = Either Self ReadExpr
  type Key ReadExpr = Ident
  Left Self #. k = ReadExpr (Var (Left (Public k)))
  Right (ReadExpr m) #. k = ReadExpr (Repr (Sel m k))

instance IsList ReadExpr where
  type Item ReadExpr = ReadStmt ReadExpr
  fromList bdy =
    readBlock (fromList bdy) (ReadExpr emptyRepr)

instance Extend_ ReadExpr where
  type Extension ReadExpr = ReadBlock
  a # ReadBlock f = f a

