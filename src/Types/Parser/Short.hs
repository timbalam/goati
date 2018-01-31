{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, StandaloneDeriving, TypeFamilies, OverloadedLists #-}
module Types.Parser.Short
  ( self_
  , env_
  , symbol_
  , block_
  , tup_
  , not_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  , (#), (#=)
  )
where
import Types.Parser

import qualified Data.Text as T
import Data.String( IsString(..) )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Functor.Identity
import Data.Bifunctor
import Control.Applicative( liftA2 )
import Control.Monad.Free
import Control.Monad.State
import Control.Monad( join )
import GHC.Exts( IsList(..) )

infixl 9 #., #, #.#
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

instance IsPublic Tag where self_ = Ident

instance IsPublic Var where self_ = Pub . self_
instance IsPrivate Var where env_ = Priv
  
instance IsPublic b => IsPublic (Path b) where self_ = Pure . self_
instance IsPrivate b => IsPrivate (Path b) where  env_ = Pure . env_
  
instance IsPublic Syntax where self_ = Var . self_
instance IsPrivate Syntax where env_ = Var . env_
  
instance IsPublic (Stmt a) where self_ = Pun . self_
instance IsPrivate (Stmt a) where env_ = Pun . env_
  
instance IsPublic SetExpr where self_ = SetPath . self_
instance IsPrivate SetExpr where env_ = SetPath . env_


-- | Overload symbol addressing
class IsSymbol a where symbol_ :: T.Text -> a

instance IsSymbol Symbol where symbol_ = S_
instance IsSymbol RecStmt where symbol_ = DeclSym . symbol_
  
  
-- | Overload field address operation
class HasField a where
  has :: a -> T.Text -> a
  hasid :: a -> Symbol -> a
class HasField p => IsPath p a | a -> p where fromPath :: p -> a

instance HasField (Path a) where
  has b x = Free (b `At` Ident x)
  hasid b s = Free (b `At` Symbol s)
instance IsPath (Path a) (Path a) where fromPath = id

instance HasField Syntax where
  has a x = Get (a `At` Ident x)
  hasid a s = Get (a `At` Symbol s)
instance IsPath Syntax Syntax where fromPath = id
  
instance IsPath VarPath (Stmt a) where fromPath = Pun
  
instance IsPath VarPath SetExpr where fromPath = SetPath

  
(#.) :: IsPath p a => p -> T.Text -> a
a #. x = fromPath (has a x)

(#.#) :: IsPath p a => p -> Symbol -> a
a #.# e = fromPath (hasid a e)
 
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
  block_ :: [RecStmt] -> a
  
  
instance IsBlock Block where
  block_ = Rec
 
  
instance IsBlock Syntax where
  block_ = Block . block_


-- | Constructor for non-recursively scoped part of block
class IsTuple a where
  type TupleStmt a
  tup_ :: [TupleStmt a] -> a
  

instance IsTuple Block where
  type (TupleStmt Block) = Stmt Syntax
  tup_ = Tup
  
  
instance IsTuple Syntax where
  type (TupleStmt Syntax) = Stmt Syntax
  tup_ = Block . tup_
  
  
instance IsTuple SetExpr where
  type (TupleStmt SetExpr) = Stmt SetExpr
  tup_ = Decomp
  
  
newtype ST_ = ST_ [Stmt SetExpr]

instance IsTuple ST_ where 
  type (TupleStmt ST_) = Stmt SetExpr
  tup_ = ST_
  
  
-- | Juxtaposition operator
class Extends a where
  type Fields a
  extend :: a -> Fields a -> a
  
  
instance Extends Syntax where
  type (Fields Syntax) = Block
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

instance IsAssign RecStmt where
  type (Lhs RecStmt) = SetExpr
  type (Rhs RecStmt) = Syntax
  fromAssign = SetRec
  
instance IsAssign (Stmt a) where
  type (Lhs (Stmt a)) = Path Tag
  type (Rhs (Stmt a)) = a
  fromAssign = Set

  
(#=) :: IsAssign s => Lhs s -> Rhs s -> s
(#=) = fromAssign
  



