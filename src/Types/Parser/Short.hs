{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, StandaloneDeriving, TypeFamilies #-}
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
import Control.Monad.Free
--import Control.Monad.State
--import Control.Monad( join )

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

instance IsPublic (Key a) where self_ = Ident

instance IsPublic b => IsPublic (Vis a b) where self_ = Pub . self_
instance IsPrivate (Vis Ident a) where env_ = Priv
  
instance IsPublic b => IsPublic (Path a b) where self_ = Pure . self_
instance IsPrivate b => IsPrivate (Path a b) where  env_ = Pure . env_
  
instance IsPublic Syntax where self_ = Var . self_
instance IsPrivate Syntax where env_ = Var . env_
  
instance IsPublic a => IsPublic (Stmt a b) where self_ = Pun . self_
instance IsPrivate (Stmt a b) where env_ = Pun . env_
  
instance IsPublic a => IsPublic (SetExpr a) where self_ = SetPath . self_
instance IsPrivate (SetExpr a) where env_ = SetPath . env_


-- | Overload symbol addressing
class IsSymbol a where symbol_ :: T.Text -> a

instance IsSymbol Symbol where symbol_ = S_
instance IsSymbol (RecStmt k a) where symbol_ = DeclSym . symbol_
  
  
-- | Overload field address operation
class HasField a where
  has :: a -> T.Text -> a
  hasid :: a -> Symbol -> a
  
class HasField (PathOf a) => IsPath a where
  type PathOf a
  fromPath :: PathOf a -> a

  
instance HasField (Path Tag a) where
  has b x = Free (b `At` Ident x)
  hasid b s = Free (b `At` Symbol s)
  
instance IsPath (Path Tag a) where
  type (PathOf (Path Tag a)) = Path Tag a
  fromPath = id

  
instance HasField (Expr Tag a) where
  has a x = Get (a `At` Ident x)
  hasid a s = Get (a `At` Symbol s)
  
instance IsPath Syntax where
  type (PathOf Syntax) = Syntax
  fromPath = id
  
  
instance IsPath (Stmt Tag a) where
  type (PathOf (Stmt Tag a)) = VarPath
  fromPath = Pun
  
instance IsPath (SetExpr Tag) where
  type (PathOf (SetExpr Tag)) = VarPath 
  fromPath = SetPath

  
(#.) :: IsPath a => PathOf a -> T.Text -> a
a #. x = fromPath (has a x)

(#.#) :: IsPath a => PathOf a -> Symbol -> a
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
  block_ :: [RecStmt Tag Syntax] -> a
  
  
instance IsBlock (Block Tag Syntax) where
  block_ = Rec
 
  
instance IsBlock Syntax where
  block_ = Block . block_


-- | Constructor for non-recursively scoped part of block
class IsTuple a where
  type TupleOf a
  tup_ :: [TupleOf a] -> a
  

instance IsTuple (Block Tag Syntax) where
  type (TupleOf (Block Tag Syntax)) = Stmt Tag Syntax
  tup_ = Tup
  
  
instance IsTuple Syntax where
  type (TupleOf Syntax) = Stmt Tag Syntax
  tup_ = Block . tup_
  
  
instance IsTuple (SetExpr Tag) where
  type (TupleOf (SetExpr Tag)) = Stmt Tag (SetExpr Tag)
  tup_ = Decomp
  
  
-- | Dummy type so that tup_ constructor works on left hand of assignment
newtype ST_ = ST_ [Stmt Tag (SetExpr Tag)]

instance IsTuple ST_ where 
  type (TupleOf ST_) = Stmt Tag (SetExpr Tag)
  tup_ = ST_
  
  
-- | Juxtaposition operator
class Extends a where
  type Fields a
  extend :: a -> Fields a -> a
  
  
instance Extends Syntax where
  type (Fields Syntax) = Block Tag Syntax
  extend = Extend
  
  
instance Extends (SetExpr Tag) where
  type (Fields (SetExpr Tag)) = ST_
  extend se (ST_ xs) = SetDecomp se xs
  
  
(#) :: Extends a => a -> Fields a -> a
(#) = extend
  
  
-- | Overload assignment operator
class IsAssign s where
  type (Lhs s)
  type (Rhs s)
  fromAssign :: Lhs s -> Rhs s -> s

instance IsAssign (RecStmt Tag Syntax) where
  type (Lhs (RecStmt Tag Syntax)) = SetExpr Tag
  type (Rhs (RecStmt Tag Syntax)) = Syntax
  fromAssign = SetRec
  
instance IsAssign (Stmt Tag a) where
  type (Lhs (Stmt Tag a)) = Path Tag Tag
  type (Rhs (Stmt Tag a)) = a
  fromAssign = Set

  
(#=) :: IsAssign s => Lhs s -> Rhs s -> s
(#=) = fromAssign
  



