{-# LANGUAGE OverloadedStrings, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving, StandaloneDeriving #-}
module Types.Parser.Short
  ( IsPublic( self_ )
  , IsPrivate( env_ )
  , IsSymbol( symbol_ )
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
import Control.Applicative( liftA2 )
import Control.Monad.Free
import Control.Monad.State
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
class IsPublic a where self_ :: Applicative m => T.Text -> m a
class IsPrivate a where env_ :: Applicative m => T.Text -> m a

instance IsPublic Tag where self_ = pure . Label

instance IsPublic Var where self_ = fmap Pub . self_
instance IsPrivate Var where env_ = pure . Priv
  
instance IsPublic b => IsPublic (Path b) where self_ = fmap Pure . self_
instance IsPrivate b => IsPrivate (Path b) where env_ = fmap Pure . env_
  
instance IsPublic Syntax where self_ = fmap Var . self_
instance IsPrivate Syntax where env_ = fmap Var . env_
  
instance IsPublic Stmt where self_ = fmap SetPun . self_
instance IsPrivate Stmt where env_ = fmap SetPun . env_
  
instance IsPublic SetExpr where self_ = fmap SetPath . self_
instance IsPrivate SetExpr where env_ = fmap SetPath . env_
  
instance IsPublic MatchStmt where self_ = fmap MatchPun . self_
instance IsPrivate MatchStmt where env_ = fmap MatchPun . env_


-- | Overload symbol addressing
class IsSymbol a where symbol_ :: T.Text -> a

instance Applicative m => IsSymbol (m Symbol) where symbol_ = pure . S
instance IsSymbol (State Id Stmt) where
  symbol_ s = DeclSym <$> symbol_ s <*> get <* modify' succ
  
  
-- | Overload field address operation
class HasField a where
  has :: Functor m => m a -> T.Text -> m a
  hasid :: Functor m => m a -> Symbol -> m a
class HasField p => IsPath p a | a -> p where fromPath :: p -> a

instance HasField (Path a) where
  has b x = Free . (`At` Label x) <$> b
  hasid b s = Free . (`At` Symbol s) <$> b
instance IsPath (Path a) (Path a) where fromPath = id
  
instance HasField Syntax where
  has a x = Get . (`At` Label x) <$> a
  hasid a s = Get . (`At` Symbol s) <$> a
instance IsPath Syntax Syntax where fromPath = id
  
instance IsPath (Path Var) Stmt where fromPath = SetPun
  
instance IsPath (Path Var) SetExpr where fromPath = SetPath
  
instance IsPath (Path Var) MatchStmt where fromPath = MatchPun

  
(#.) :: (IsPath p a, Functor m) => m p -> T.Text -> m a
a #. x = fromPath <$> has a x

(#.#) :: (IsPath p a, Functor m) => m p -> Symbol -> m a
a #.# e = fromPath <$> hasid a e
 
-- | Overload literal numbers and strings
instance Num Syntax where
  fromInteger = IntegerLit
  (+) = error "Num Syntax"
  (-) = error "Num Syntax"
  (*) = error "Num Syntax"
  negate = Unop Neg
  abs = error "Num Syntax"
  signum = error "Num Syntax"
  
  
instance Applicative m => Num (m Syntax) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  

instance Fractional Syntax where
  fromRational = NumberLit . fromRational
  (/) = error "Fractional Syntax"
  
  
instance Applicative m => Fractional (m Syntax) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)

  
instance IsString Syntax where
  fromString = StringLit . fromString
  
  
instance Applicative m => IsString (m Syntax) where
  fromString = pure . fromString


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
  
instance Operable (State s Syntax) where
  (#&) = liftA2 (#&)
  (#|) = liftA2 (#|)
  (#+) = liftA2 (#+)
  (#-) = liftA2 (#-)
  (#*) = liftA2 (#*)
  (#/) = liftA2 (#/)
  (#^) = liftA2 (#^)
  (#==) = liftA2 (#==)
  (#!=) = liftA2 (#!=)
  (#<) = liftA2 (#<)
  (#<=) = liftA2 (#<=)
  (#>) = liftA2 (#>)
  (#>=) = liftA2 (#>=)
  
  not_ = fmap not_

  
-- | Overload juxtaposition operator
class IsApply a x b | b -> a x where
  fromApply :: a -> [x] -> b
  
  
instance IsApply Syntax Stmt Syntax where
  fromApply = Extend
  
instance IsApply SetExpr MatchStmt SetExpr where
  fromApply = SetDecomp

  
(#) :: (IsApply a x b, Applicative m) => m a -> [m x] -> m b
a # xs = fromApply <$> a <*> sequenceA xs
  
  
-- | Overload assignment operator
class IsAssign l r s | s -> l r where
  fromAssign :: l -> r -> s

instance IsAssign SetExpr Syntax Stmt where fromAssign = Set

instance IsAssign (Path Tag) SetExpr MatchStmt where fromAssign = Match

  
(#=) :: (IsAssign l r s, Applicative m) => m l -> m r -> m s
(#=) = liftA2 fromAssign



