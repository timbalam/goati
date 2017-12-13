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
  
--instance IsPublic Label where self' = id
instance IsPublic (Tag a) where self' = Label
instance IsPublic (Vis a) where self' = Pub . self'
instance IsPrivate (Vis a) where env' = Priv
  
instance IsPublic b => IsPublic (Path a b) where self' = Pure . self'
instance IsPrivate b => IsPrivate (Path a b) where env' = Pure . env'
  
instance IsPublic Syntax where self' = Var . self'
instance IsPrivate Syntax where env' = Var . env'
  
instance IsPublic Stmt where self' = SetPun . self'
instance IsPrivate Stmt where env' = SetPun . env'
  
instance IsPublic SetExpr where self' = SetPath . self'
instance IsPrivate SetExpr where env' = SetPath . env'
  
instance IsPublic MatchStmt where self' = MatchPun . self'
instance IsPrivate MatchStmt where env' = MatchPun . env'
  
  
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


-- | Genericised operations
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=), (#) ::
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
(#) = Update

not' :: Syntax -> Syntax
not' = Unop Not

block' :: [Stmt] -> Syntax
block' xs = Block xs Nothing

block'' :: [Stmt] -> Syntax -> Syntax
block'' xs = Block xs . Just

setblock' :: [MatchStmt] -> SetExpr
setblock' xs = SetBlock xs Nothing

setblock'' :: [MatchStmt] -> Path Syntax (Vis Syntax) -> SetExpr
setblock'' xs = SetBlock xs . Just


-- | Overload assignment operator
class IsAssign s l r | s -> l r where
  fromAssign :: l -> r -> s

instance IsAssign Stmt SetExpr Syntax where fromAssign = Set

instance IsAssign MatchStmt (Path Syntax (Tag Syntax)) SetExpr where fromAssign = Match

  
(#=) :: IsAssign s l r => l -> r -> s
(#=) = fromAssign



