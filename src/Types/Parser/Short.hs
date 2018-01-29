{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, StandaloneDeriving, TypeFamilies, OverloadedLists #-}
module Types.Parser.Short
  ( IsPublic( self_ )
  , IsPrivate( env_ )
  , IsSymbol( symbol_ )
  , IsBlock( block_ )
  , Packable
  , Operable(..)
  , (#), (#...), (#=)
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
infixl 1 #...
infixr 0 #=


-- | Overload self and env addressing
class IsPublic a where self_ :: T.Text -> a
class IsPrivate a where env_ :: T.Text -> a

instance IsPublic Tag where self_ = Label

instance IsPublic Var where self_ = Pub . self_
instance IsPrivate Var where env_ = Priv
  
instance IsPublic b => IsPublic (Path b) where self_ = Pure . self_
instance IsPrivate b => IsPrivate (Path b) where  env_ = Pure . env_
  
instance IsPublic Syntax where self_ = Var . self_
instance IsPrivate Syntax where env_ = Var . env_
  
instance IsPublic Stmt where self_ = SetPun . self_
instance IsPrivate Stmt where env_ = SetPun . env_
  
instance IsPublic SetExpr where self_ = SetPath . self_
instance IsPrivate SetExpr where env_ = SetPath . env_
  
instance IsPublic MatchStmt where self_ = MatchPun . self_
instance IsPrivate MatchStmt where env_ = MatchPun . env_


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
  has b x = Free (b `At` Label x)
  hasid b s = Free (b `At` Symbol s)
instance IsPath (Path a) (Path a) where fromPath = id

instance HasField Syntax where
  has a x = Get (a `At` Label x)
  hasid a s = Get (a `At` Symbol s)
instance IsPath Syntax Syntax where fromPath = id
  
instance IsPath VarPath Stmt where fromPath = SetPun
  
instance IsPath VarPath SetExpr where fromPath = SetPath
  
instance IsPath VarPath MatchStmt where fromPath = MatchPun

  
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
  block_ :: Tuple -> [RecStmt] -> a
  
  
instance IsBlock Block where
  block_ t = let Tuple xs m = t in B_ xs m
  
  
instance IsBlock Syntax where
  block_ = (Block .) <$> block_


-- | Constructor for non-recursively scoped part of block
data Tuple = Tuple [Stmt] (Maybe Syntax)


instance IsList Tuple where
  type (Item Tuple) = Stmt
  fromList xs = Tuple xs Nothing
  toList = error "IsList Tuple"
  
  
instance IsList SetExpr where
  type (Item SetExpr) = MatchStmt
  fromList xs = SetBlock xs Nothing
  toList = error "IsList SetExpr"
  
  
-- | Juxtaposition operator
(#) :: Syntax -> Block -> Syntax
(#) = Extend
  
  
-- | Unpack operator
class Packable s where
  type PackWith s
  type PackInto s
  pack :: PackWith s -> PackInto s -> s
  
  
instance Packable SetExpr where
  type (PackWith SetExpr) = [MatchStmt]
  type (PackInto SetExpr) = SetExpr
  pack xs e = SetBlock xs (Just e)
  
  
instance Packable Tuple where
  type (PackWith Tuple) = [Stmt]
  type (PackInto Tuple) = Syntax
  pack stmts e = Tuple stmts (Just e)
  
  
(#...) :: Packable s => PackWith s -> PackInto s -> s
(#...) = pack
  
  
-- | Overload assignment operator
class IsAssign s where
  type (Lhs s)
  type (Rhs s)
  fromAssign :: Lhs s -> Rhs s -> s

instance IsAssign RecStmt where
  type (Lhs RecStmt) = SetExpr
  type (Rhs RecStmt) = Syntax
  fromAssign = SetRec
  
instance IsAssign Stmt where
  type (Lhs Stmt) = SetExpr
  type (Rhs Stmt) = Syntax
  fromAssign = Set

instance IsAssign MatchStmt where
  type (Lhs MatchStmt) = Path Tag
  type (Rhs MatchStmt) = SetExpr
  fromAssign = Match

  
(#=) :: IsAssign s => Lhs s -> Rhs s -> s
(#=) = fromAssign
  



