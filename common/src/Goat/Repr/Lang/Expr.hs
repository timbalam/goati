{-# LANGUAGE RankNTypes, TypeFamilies #-}
module Goat.Repr.Lang.Expr
 where

import Goat.Lang.Reflect (handleAll)
import Goat.Lang.Text (Text_(..))
import Goat.Lang.LogicB (LogicB_(..))
import Goat.Lang.ArithB (ArithB_(..))
import Goat.Lang.CmpB (CmpB_(..))
import Goat.Lang.Unop (Unop_(..))
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Field (Field_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Ident (IsString(..), Ident)
import Goat.Lang.Extern (Extern_(..))
import Goat.Lang.Expr (SomeExpr, fromExprM)
import Goat.Repr.Pattern
  ( Public(..), Local(..), Privacy
  , Declared, Multi, Pattern
  , Bindings, Block
  )
import Goat.Repr.Lang.Pattern
import Goat.Repr.Assoc (Assoc)
import Goat.Repr.Expr
  ( Repr(..), emptyRepr, Expr(..)
  , Extern(..), VarName, blockBindings
  )
import Data.These
import Data.Semigroup (Option)

import qualified Data.Text as Text

newtype ReadExpr =
  ReadExpr {
    readExpr
     :: Repr
          (Pattern (Option (Privacy These)))
          (VarName Ident Ident (Extern Ident))
    }

nume = error "Num ReadExpr"

instance Num ReadExpr where
  fromInteger d = ReadExpr (Repr (Number (fromInteger d)))
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional ReadExpr"
  
instance Fractional ReadExpr where
  fromRational r = ReadExpr (Repr (Number (fromRational r)))
  (/) = frace
  
instance Text_ ReadExpr where
  quote_ s = ReadExpr (Repr (Text (Text.pack s)))

readBinop
 :: (forall f m x . m x -> m x -> Expr f m x)
 -> ReadExpr -> ReadExpr -> ReadExpr
readBinop op (ReadExpr m) (ReadExpr n) =
  ReadExpr (Repr (m `op` n))
      
instance ArithB_ ReadExpr where
  (#+) = readBinop (:#+)
  (#-) = readBinop (:#-)
  (#*) = readBinop (:#*)
  (#/) = readBinop (:#/)
  (#^) = readBinop (:#^)
  
instance CmpB_ ReadExpr where
  (#==) = readBinop (:#==)
  (#!=) = readBinop (:#!=)
  (#<)  = readBinop (:#<)
  (#<=) = readBinop (:#<=)
  (#>)  = readBinop (:#>)
  (#>=) = readBinop (:#>=)

instance LogicB_ ReadExpr where
  (#||) = readBinop (:#||)
  (#&&) = readBinop (:#&&)

readUnop
 :: (forall f m x . m x -> Expr f m x)
 -> ReadExpr -> ReadExpr
readUnop op (ReadExpr m) = ReadExpr (Repr (op m))

instance Unop_ ReadExpr where
  neg_ = readUnop Neg
  not_ = readUnop Not
  
instance Extern_ ReadExpr where
  use_ n = ReadExpr (Var (Right (Right (Extern n))))
  
instance IsString ReadExpr where
  fromString n =
    ReadExpr (Var (Right (Left (Local (fromString n)))))

instance Field_ ReadExpr where
  type Compound ReadExpr = Relative ReadExpr
  r #. n = ReadExpr (readRel r n) where
    readRel (Parent (ReadExpr m)) n = Repr (m :#. n)
    readRel Self n = Var (Left (Public n))

instance Block_ ReadExpr where
  type Stmt ReadExpr = ReadDefn ReadExpr
  block_ bdy = readBlock (block_ bdy) (ReadExpr emptyRepr)

instance Extend_ ReadExpr where
  type Extension ReadExpr = ReadBlock
  type Ext ReadExpr = ReadExpr
  a # ReadBlock f = f a

-- | Proof of instance 'Expr_ ReadExpr' with 'Compound ReadExpr ~ Relative ReadExpr', 'Extension ReadExpr ~ ReadBlock', 'Ext ReadExpr ~ ReadExpr' and 'Stmt ReadExpr ~ ReadDefn'
readExprProof
 :: SomeExpr (Relative ReadExpr) ReadExpr ReadBlock ReadDefn
 -> ReadExpr
readExprProof = handleAll fromExprM

newtype ReadBlock =
  ReadBlock { readBlock :: ReadExpr -> ReadExpr }

instance Block_ ReadBlock where
  type Stmt ReadBlock = ReadDefn
  block_ bdy =
    ReadBlock
      (ReadExpr .
        blockBindings (foldMap readDefn bdy) .
        readExpr)


newtype ReadDefn a =
  ReadDefn {
    readDefn
     :: Bindings
          (Multi (Declared Assoc (Privacy These)))
          (Pattern (Option (Privacy These)) ())
          (Repr (Pattern (Option (Privacy These))))
          a
    }
  
punStmt :: Pun ReadChain a -> ReadDefn a
punStmt = pun (setPattern . setPath . publicChain) id
    
instance IsString (ReadDefn a) where
  fromString s = punStmt (fromString s)

instance Field_ (ReadDefn a) where
  type Compound (ReadDefn a) =
    Pun (Relative ReadChain) (Relative a)
  r #. i = punStmt (r #. i)

instance Let_ (ReadDefn a) where
  type Lhs (ReadDefn a) = ReadPattern
  type Rhs (ReadDefn a) = a
  ReadPattern f #= ReadExpr a = ReadDefn (f a)

