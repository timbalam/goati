{-# LANGUAGE RankNTypes, TypeFamilies #-}
module Goat.Repr.Expr.Lang
 where

import Goat.Comp (run)
import Goat.Repr.Pattern
import Goat.Repr.Pattern.Lang
import Goat.Repr.Expr
import Goat.Lang.Text (Text_(..))
import Goat.Lang.LogicB (LogicB_(..))
import Goat.Lang.ArithB (ArithB_(..))
import Goat.Lang.CmpB (CmpB_(..))
import Goat.Lang.Unop (Unop_(..))
import Goat.Lang.Let (Let_(..), SomeDefn, fromDefn)
import Goat.Lang.Field (Field_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Extern (Extern_(..))
import Goat.Lang.Expr (SomeExpr, fromExpr)
import Data.These

import qualified Data.Text as Text

newtype ReadExpr =
  ReadExpr {
    readExpr
     :: Repr
          (Multi
            (IdxBindings 
              (Declared These Assoc)
              (Pattern (Multi (Declared These Assoc)))))
          (VarName ())
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
 :: (forall r m x . m x -> m x -> Expr r m x)
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
 :: (forall r m x . m x -> Expr r m x)
 -> ReadExpr -> ReadExpr
readUnop op (ReadExpr m) = ReadExpr (Repr (op m))

instance Unop_ ReadExpr where
  neg_ = readUnop Neg
  not_ = readUnop Not
  
instance Extern_ ReadExpr where
  use_ n = ReadExpr (Var (Right (Left (Extern n))))
  
instance IsString ReadExpr where
  fromString n =
    ReadExpr (Var (Right (Right (Local (fromString n)))))

instance Field_ ReadExpr where
  type Compound ReadExpr = Relative ReadExpr
  r #. n = ReadExpr (Repr (readRel r :#. n)) where
    readRel (Parent (ReadExpr m)) = m
    readRel Self = Var (Left (Public ()))

instance Block_ ReadExpr where
  type Stmt ReadExpr = ReadDefn
  block_ bdy = ReadExpr (Repr (Block abs))
    where
      abs =
        abstractDeclared
          readExpr
          (Multi (crosswalkDuplicates readDefn bdy))
  
      
instance Extend_ ReadExpr where
  type Ext ReadExpr = ReadExpr
  (#) = readBinop (:#)

readExprProof :: SomeExpr ReadDefn -> ReadExpr
readExprProof = run . fromExpr id


newtype ReadDefn =
  ReadDefn {
    readDefn
     :: IdxBindings
          (Declared These Assoc)
          (Pattern (Multi (Declared These Assoc)))
          ReadExpr
    }
  
punStmt :: Pun ReadChain ReadExpr -> ReadDefn
punStmt = pun (setPattern . setPath . publicChain) id
    
instance IsString ReadDefn where
  fromString s = punStmt (fromString s)

instance Field_ ReadDefn where
  type Compound ReadDefn =
    Pun (Relative ReadChain) (Relative ReadExpr)
  r #. i = punStmt (r #. i)

instance Let_ ReadDefn where
  type Lhs ReadDefn = ReadPattern
  type Rhs ReadDefn = ReadExpr
  ReadPattern f #= a = ReadDefn (f a)

readDefnProof :: SomeDefn -> ReadDefn
readDefnProof = run . fromDefn


