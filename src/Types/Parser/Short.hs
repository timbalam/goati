{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies #-}
module Types.Parser.Short
  ( IsPublic( self' )
  , IsPrivate( env' )
  , not', block', setblock', block'', setblock''
  , (#=), (#.), (#.#)
  , (#^), (#*), (#/), (#+), (#-)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  , (#&), (#|), (#)
  , module Types.Parser
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
class IsPublic a where self' :: T.Text -> a
class IsPrivate a where env' :: T.Text -> a
  
instance IsPublic Tag where self' = id
instance IsPublic (Vis Tag) where self' = Pub
instance IsPrivate (Vis Tag) where env' = Priv
  
instance IsPublic a => IsPublic (Path a) where self' = Pure . self'
instance IsPrivate a => IsPrivate (Path a) where env' = Pure . env'
  
instance IsPublic a => IsPublic (Expr a) where self' = Var . self'
instance IsPrivate a => IsPrivate (Expr a) where env' = Var . env'
  
instance IsPublic a => IsPublic (Stmt a) where self' = SetPun . self'
instance IsPrivate a => IsPrivate (Stmt a) where env' = SetPun . env'
  
instance IsPublic a => IsPublic (SetExpr a) where self' = SetPath . self'
instance IsPrivate a => IsPrivate (SetExpr a) where env' = SetPath . env'
  
instance IsPublic a => IsPublic (MatchStmt a) where self' = MatchPun . self'
instance IsPrivate a => IsPrivate (MatchStmt a) where env' = MatchPun . env'
  
  
-- | Overload field address operation
class HasField f where
  has :: f a -> T.Text -> f a
  id :: f a -> Expr (Vis Tag)
class HasField f => IsPath f g | g -> f where fromPath :: f a -> g a

instance HasField Path where has a x = Free (a `At` x)
instance IsPath Path Path where fromPath = id
  
instance HasField Expr where has a x = Get (a `At` x)
instance IsPath Expr Expr where fromPath = id
  
instance IsPath Path Stmt where fromPath = SetPun
  
instance IsPath Path SetExpr where fromPath = SetPath
  
instance IsPath Path MatchStmt where fromPath = MatchPun

  
(#.) :: IsPath f g => f a -> T.Text -> g a
a #. x = fromPath (has a x)

(#.#) :: 
 
-- | Overload literal numbers and strings
instance Num (Expr a) where
  fromInteger = IntegerLit
  (+) = error "Num Expr"
  (-) = error "Num Expr"
  (*) = error "Num Expr"
  negate = Unop Neg
  abs = error "Num Expr"
  signum = error "Num Expr"
  

instance Fractional (Expr a) where
  fromRational = NumberLit . fromRational
  (/) = error "Fractional Expr"

  
instance IsString (Expr a) where
  fromString = StringLit . fromString


-- | Genericised operations
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=), (#) ::
  Expr (Vis Tag) -> Expr (Vis Tag) -> Expr (Vis Tag)
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
(#) = Update

not' :: Expr (Vis Tag) -> Expr (Vis Tag)
not' = Unop Not


block' :: [Stmt (Vis Tag)] -> Expr (Vis Tag)
block' xs = Block xs Nothing


block'' :: [Stmt (Vis Tag)] -> Expr (Vis Tag) -> Expr (Vis Tag)
block'' xs = Block xs . Just


setblock' :: [MatchStmt (Vis Tag)] -> SetExpr (Vis Tag)
setblock' xs = SetBlock xs Nothing


setblock'' :: [MatchStmt (Vis Tag)] -> Path (Vis Tag) -> SetExpr (Vis Tag)
setblock'' xs = SetBlock xs . Just


-- | Overload assignment operator
class IsAssign s l r | s -> l r where
  fromAssign :: l -> r -> s

instance IsAssign (Stmt a) (SetExpr a) (Expr a) where fromAssign = Set

instance IsAssign (MatchStmt a) (Path Tag) (SetExpr a) where fromAssign = Match

  
(#=) :: IsAssign s l r => l -> r -> s
(#=) = fromAssign



