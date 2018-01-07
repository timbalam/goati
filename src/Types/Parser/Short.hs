{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies #-}
module Types.Parser.Short
  ( IsPublic( self_ )
  , IsPrivate( env_ )
  , not_
  , (#=), (#.), (#.#)
  , (#^), (#*), (#/), (#+), (#-)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  , (#&), (#|), (#)
  )
where
import Types.Parser

import qualified Data.Text as T
import Data.String( IsString(..) )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Functor.Identity
import Control.Monad.Free
import Control.Monad( join )
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
  
--instance IsPublic Label where self_ = id
instance IsPublic (Tag a) where self_ = Label
instance IsPublic (Vis a) where self_ = Pub . self_
instance IsPrivate (Vis a) where env_ = Priv
instance IsPublic a => IsPublic (Sym a) where  self_ = In . self_
instance IsPrivate a => IsPrivate (Sym a) where env_ = In . env_
  
instance IsPublic b => IsPublic (Path a b) where self_ = Pure . self_
instance IsPrivate b => IsPrivate (Path a b) where env_ = Pure . env_
  
instance IsPublic Syntax where self_ = Var . self_
instance IsPrivate Syntax where env_ = Var . env_
  
instance IsPublic Stmt where self_ = SetPun . self_
instance IsPrivate Stmt where env_ = SetPun . env_
  
instance IsPublic SetExpr where self_ = SetPath . self_
instance IsPrivate SetExpr where env_ = SetPath . env_
  
instance IsPublic MatchStmt where self_ = MatchPun . self_
instance IsPrivate MatchStmt where env_ = MatchPun . env_
  
  
-- | Overload field address operation
class HasField a where
  has :: a -> T.Text -> a
  hasid :: a -> Syntax -> a
class HasField p => IsPath p a | a -> p where fromPath :: p -> a

instance HasField (Path Syntax a) where
  has b x = Free (b `At` Label x)
  hasid b e = Free (b `At` Id e)
instance IsPath (Path Syntax a) (Path Syntax a) where fromPath = id
  
instance HasField Syntax where
  has a x = Get (a `At` Label x)
  hasid a e = Get (a `At` Id e)
instance IsPath Syntax Syntax where fromPath = id
  
instance IsPath (Path Syntax (Vis Syntax)) Stmt where fromPath = SetPun
  
instance IsPath (Path Syntax (Vis Syntax)) SetExpr where fromPath = SetPath
  
instance IsPath (Path Syntax (Vis Syntax)) MatchStmt where fromPath = MatchPun

  
(#.) :: IsPath p a => p -> T.Text -> a
a #. x = fromPath (has a x)

(#.#) :: IsPath p a => p -> Syntax -> a
a #.# e = fromPath (hasid a e)
 
-- | Overload literal numbers and strings
instance Num Syntax where
  fromInteger = IntegerLit
  (+) = error "Num Expr"
  (-) = error "Num Expr"
  (*) = error "Num Expr"
  negate = Unop Neg
  abs = error "Num Expr"
  signum = error "Num Expr"
  

instance Fractional Syntax where
  fromRational = NumberLit . fromRational
  (/) = error "Fractional Expr"

  
instance IsString Syntax where
  fromString = StringLit . fromString


-- | Operators
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=) ::
  Syntax -> Syntax -> Syntax
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

not_ :: Syntax -> Syntax
not_ = Unop Not

-- | Overload juxtaposition operator
class IsApply a x b | b -> a x where
  fromApply :: a -> x -> b
  
  
instance IsApply Syntax [Stmt] Syntax where
  fromApply = Extend
  
instance IsApply SetExpr [MatchStmt] SetExpr where
  fromApply = SetDecomp

  
(#) :: IsApply a x b => a -> x -> b
(#) = fromApply
  
  
-- | Overload assignment operator
class IsAssign s l r | s -> l r where
  fromAssign :: l -> r -> s

instance IsAssign Stmt SetExpr Syntax where fromAssign = Set

instance IsAssign MatchStmt (Path Syntax (Tag Syntax)) SetExpr where fromAssign = Match

  
(#=) :: IsAssign s l r => l -> r -> s
(#=) = fromAssign



