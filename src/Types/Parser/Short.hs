{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, StandaloneDeriving, TypeFamilies #-}
module Types.Parser.Short
  ( self_
  , env_
  , block_
  , tup_
  , use_
  , not_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  , (#), (#=), (#.)
  )
where
import Types.Parser

import Data.Bifunctor
import qualified Data.Text as T
import Data.String( IsString(..) )
import Data.List.NonEmpty( NonEmpty(..) )
--import Control.Monad.Free

infixl 9 #., #
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>
infixr 3 #&
infixr 2 #|
infixr 0 #=


-- | Overload self and env addressing
class IsPublic a where self_ :: T.Text -> a
class IsPrivate a where env_ :: T.Text -> a

instance IsPublic Key where self_ = K_
instance IsPrivate Ident where env_ = id

instance IsPublic b => IsPublic (Vis a b) where self_ = Pub . self_
instance IsPrivate a => IsPrivate (Vis a b) where env_ = Priv . env_

instance IsPublic a => IsPublic (Res a b) where self_ = In . self_
instance IsPrivate a => IsPrivate (Res a b) where env_ = In . env_
  
instance IsPublic b => IsPublic (Path b) where self_ = Pure . self_
instance IsPrivate b => IsPrivate (Path b) where  env_ = Pure . env_
  
instance IsPublic Syntax where self_ = Var . self_
instance IsPrivate Syntax where env_ = Var . env_

instance IsPublic (RecStmt b) where self_ = DeclVar . self_
  
instance IsPublic (Stmt b) where self_ = Pun . self_
instance IsPrivate (Stmt b) where env_ = Pun . env_
  
instance IsPublic SetExpr where self_ = SetPath . self_
instance IsPrivate SetExpr where env_ = SetPath . env_


-- | Overload import syntax
class IsImport a where use_ :: T.Text -> a 

instance IsImport Import where use_ = Use
instance IsImport b => IsImport (Res a b) where use_ = Ex . use_
  
  
-- | Overload field address operation
class HasField a where
  has :: a -> T.Text -> a
  
class HasField (PathOf a) => IsPath a where
  type PathOf a
  fromPath :: PathOf a -> a

  
instance HasField (Path a) where
  has b x = Free (b `At` K_ x)
  
instance IsPath (Path a) where
  type (PathOf (Path a)) = Path a
  fromPath = id

  
instance HasField (Expr a) where
  has a x = Get (a `At` K_ x)
  
instance IsPath Syntax where
  type (PathOf Syntax) = Syntax
  fromPath = id
  
  
instance (HasField a, HasField b) => HasField (Vis a b) where
  has p x = bimap (`has` x) (`has` x) p
  
  
instance IsPath (Stmt a) where
  type (PathOf (Stmt a)) = VarPath
  fromPath = Pun
  
instance IsPath SetExpr where
  type (PathOf SetExpr) = VarPath 
  fromPath = SetPath
  
instance IsPath (RecStmt a) where
  type (PathOf (RecStmt a)) = Path Key
  fromPath = DeclVar

  
(#.) :: IsPath a => PathOf a -> T.Text -> a
a #. x = fromPath (has a x)
 
 
-- | Overload literal numbers and strings
instance Num Syntax where
  fromInteger = IntegerLit
  (+) = error "Num Syntax"
  (-) = error "Num Syntax"
  (*) = error "Num Syntax"
  negate = Unop Neg
  abs = error "Num Syntax"
  signum = error "Num Syntax"
  

instance Fractional Syntax where
  fromRational = NumberLit . fromRational
  (/) = error "Fractional Syntax"

  
instance IsString Syntax where
  fromString = StringLit . fromString


-- | Operators
class Operable a where
  (#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=) ::
    a -> a -> a
  not_ :: a -> a
  
instance Operable Syntax where
  (#&) = Binop And
  (#|) = Binop Or
  (#+) = Binop Add
  (#-) = Binop Sub
  (#*) = Binop Prod
  (#/) = Binop Div
  (#^) = Binop Pow
  (#==) = Binop Eq
  (#!=) = Binop Ne
  (#<) = Binop Lt
  (#<=) = Binop Le
  (#>) = Binop Gt
  (#>=) = Binop Ge
  
  not_ = Unop Not
  

-- | Overloaded block constructor
class IsBlock a where
  block_ :: [RecStmt Syntax] -> a
  
  
instance IsBlock (Block Syntax) where
  block_ = Rec
 
  
instance IsBlock Syntax where
  block_ = Block . block_


-- | Constructor for non-recursively scoped part of block
class IsTuple a where
  type TupleOf a
  tup_ :: [TupleOf a] -> a
  

instance IsTuple (Block Syntax) where
  type (TupleOf (Block Syntax)) = Stmt Syntax
  tup_ = Tup
  
  
instance IsTuple Syntax where
  type (TupleOf Syntax) = Stmt Syntax
  tup_ = Block . tup_
  
  
instance IsTuple SetExpr where
  type (TupleOf SetExpr) = Stmt SetExpr
  tup_ = Decomp
  
  
-- | Dummy type so that tup_ constructor works on left hand of assignment
newtype ST_ = ST_ [Stmt SetExpr]

instance IsTuple ST_ where 
  type (TupleOf ST_) = Stmt SetExpr
  tup_ = ST_
  
  
-- | Juxtaposition operator
class Extends a where
  type Fields a
  extend :: a -> Fields a -> a
  
  
instance Extends Syntax where
  type (Fields Syntax) = Block Syntax
  extend = Extend
  
  
instance Extends SetExpr where
  type (Fields SetExpr) = ST_
  extend se (ST_ xs) = SetDecomp se xs
  
  
(#) :: Extends a => a -> Fields a -> a
(#) = extend
  
  
-- | Overload assignment operator
class IsAssign s where
  type (Lhs s)
  type (Rhs s)
  fromAssign :: Lhs s -> Rhs s -> s

instance IsAssign (RecStmt Syntax) where
  type (Lhs (RecStmt Syntax)) = SetExpr
  type (Rhs (RecStmt Syntax)) = Syntax
  fromAssign = SetRec
  
instance IsAssign (Stmt a) where
  type (Lhs (Stmt a)) = Path Key
  type (Rhs (Stmt a)) = a
  fromAssign = Set

  
(#=) :: IsAssign s => Lhs s -> Rhs s -> s
(#=) = fromAssign


