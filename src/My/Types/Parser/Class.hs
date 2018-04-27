{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FunctionalDependencies #-}

-- | Final encoding of my language syntax
module My.Types.Parser.Class
  ( module My.Types.Parser
  , LitExpr(..)
  , OpExpr(..)
  , VarExpr(..)
  , SubExpr(..)
  , GroupExpr(..)
  , Syntax(..)
  , Path(..)
  , Rec(..)
  , Tup(..)
  , Patt(..)
  , Program(..)
  ) where
import qualified Data.Text as T
import Data.Semigroup (Semigroup)
import My.Types.Parser
  ( Ident(..)
  , Key(..)
  , Import(..)
  , Vis(..)
  , Res(..)
  , Name
  , Unop(..)
  , Binop(..)
  , StringExpr
  , prec
  )
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
class LitExpr r where
  integerLit :: Integer -> r
  numberLit :: Double -> r
  stringLit :: StringExpr -> r
  
class OpExpr r where
  unop :: Unop -> r -> r
  binop :: Binop -> r -> r -> r
  
class VarExpr r a | r -> a where
  var :: a -> r
  
class SubExpr r where
  get :: r -> Key -> r
  
class GroupExpr r g | r -> g where
  group :: g -> r
  extend :: r -> g -> r
  
  
-- | Combination of syntax features 
class (LitExpr r, OpExpr r, SubExpr r, VarExpr r a, GroupExpr r g, Rec g r, Tup g r, Monoid g) => Syntax r g a
instance (LitExpr r, OpExpr r, SubExpr r, VarExpr r a, GroupExpr r g, Rec g r, Tup g r, Monoid g) => Syntax r g a where


-- | A path expression for my language recursively describes a set of
-- nested fields relative to a self- or environment-defined field
class Monad m => Path m where
  at :: a -> Key -> m a

-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
class Rec g a | g -> a where
  decl :: (forall m . Path m => m Key) -> g
  letrec :: (forall p. Patt p => p) -> a -> g
  
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
class Tup g a | g -> a where
  pun :: (forall m . Path m => Vis (m Ident) (m Key)) -> g
  let_ :: (forall m . Path m => m Key) -> a -> g
  

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Decompose pattern (matches a set of paths to corresponding nested patterns)
--   * A decompose pattern with left over pattern (matches set of fields not
--      matched by the decompose pattern)
class Patt p where
  letpath :: (forall m . Path m => Vis (m Ident) (m Key)) -> p
  ungroup :: (forall g . (Tup g p, Monoid g) => g) -> p
  letungroup :: p -> (forall g. (Tup g p, Monoid g) => g) -> p

  
-- | A program guaranteed to be a non-empty set of top level
--  recursive statements with an optional initial global import
class VarExpr r (Name Ident Key a) => Program r a where
  program 
    :: Maybe a
    -> (forall g . (Rec g r, Semigroup g) => g)
    -> r
