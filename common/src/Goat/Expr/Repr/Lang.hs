{-# LANGUAGE RankNTypes, TypeFamilies #-}
module Goat.Expr.Repr.Lang
 where

import Goat.Comp
import Goat.Expr.Pattern
import Goat.Expr.Pattern.Lang
import Goat.Expr.Repr
import Goat.Lang.Text (Text_(..))
import Goat.Lang.LogicB (LogicB_(..))
import Goat.Lang.ArithB (ArithB_(..))
import Goat.Lang.CmpB (CmpB_(..))
import Goat.Lang.Unop (Unop_(..))
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Field (Field_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Extern (Extern_(..))
import Data.These

import qualified Data.Text as Text

newtype ReadExpr =
  ReadExpr {
    readExpr
     :: Repr
          (Multi
            (IdxBindings 
              (Definitions These Assoc)
              (Pattern (Multi (Definitions These Assoc)))))
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
  type Stmt ReadExpr = ReadStmt
  block_ bdy = ReadExpr (Repr (Block abs))
    where
      abs =
        abstractDefinitions
          readExpr
          (Multi (crosswalkDuplicates readStmt bdy))
  
      
instance Extend_ ReadExpr where
  type Ext ReadExpr = ReadExpr
  (#) = readBinop (:#)


newtype ReadStmt =
  ReadStmt {
    readStmt
     :: IdxBindings
          (Definitions These Assoc)
          (Pattern (Multi (Definitions These Assoc)))
          ReadExpr
    }
  
punStmt :: Pun ReadChain ReadExpr -> ReadStmt
punStmt = pun (setPattern . setPath . publicChain) id
    
instance IsString ReadStmt where
  fromString s = punStmt (fromString s)

instance Field_ ReadStmt where
  type Compound ReadStmt =
    Pun (Relative ReadChain) (Relative ReadExpr)
  r #. i = punStmt (r #. i)

instance Let_ ReadStmt where
  type Lhs ReadStmt = ReadPattern
  type Rhs ReadStmt = ReadExpr
  ReadPattern f #= a = ReadStmt (f a)

