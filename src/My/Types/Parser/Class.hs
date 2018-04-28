{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies #-}

-- | Final encoding of my language syntax
--
-- A set of classes corresponding to particular syntactic language features
module My.Types.Parser.Class
  ( module My.Types.Parser
  , Lit(..), Op(..)
  , Local(..), Self(..), Extern(..), Field(..)
  , Tuple(..), Block(..)
  , Extend(..), Member
  , LocalPath, RelPath, VarPath
  , Syntax
  , Let(..)
  , RecStmt, TupStmt, Patt
  , Program(..)
  ) where
import qualified Data.Text as T
import Data.Semigroup (Semigroup)
import My.Types.Parser
  ( Ident(..)
  , Key(..)
  , Import(..)
  , Unop(..)
  , Binop(..)
  , StringExpr
  )
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
class
  ( Lit r, Op r, Local r, Self r, Extern r, Field r
  , Tuple r, Block r, Member r ~ r
  , Extend r, Tuple (Group r), Block (Group r), Member (Group r) ~ r
  ) => Syntax r


-- | Literal forms
class Lit r where
  int_ :: Integer -> r
  num_ :: Double -> r
  str_ :: StringExpr -> r
  
-- | Unary and binary operators
class Op r where
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r

-- | Use a environment-bound name
class Local r where
  local_ :: Ident -> r
  
-- | Use a self-bound name
class Self r where
  self_ :: Key -> r
  
-- | Use an external name
class Extern r where
  import_ :: Import -> r
  
-- | Use a name of a component of a compound type
class Field r where
  at_ :: r -> Key -> r
  
-- | A 'path' of nested fields of an environment-bound name
class (Local r, Field r) => LocalPath r

-- | A path of a self-bound name
class (Self r, Field r) => RelPath r

-- | A 'path' of either self- or environment-bound name
class (RelPath r, LocalPath r) => VarPath r
  
-- | A value assignable in a name group
type family Member r
  
-- | Construct a tuple
class (TupStmt (Tup r), Monoid (Tup r), Rhs (Tup r) ~ Member r) => Tuple r where
  type Tup r
  
  tup_ :: Tup r -> r
  
-- | Construct a block
class (RecStmt (Rec r), Monoid (Rec r), Rhs (Rec r) ~ Member r) => Block r where
  type Rec r
  
  block_ :: Rec r -> r
  
-- | Extend a value with a new name group
class Extend r where
  type Group r
  
  ext_ :: r -> Group r -> r
  
-- | Assignment
class Let s where
  type Lhs s
  type Rhs s
  
  let_ :: Lhs s -> Rhs s -> s


-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
class (RelPath s, Let s, Patt (Lhs s)) => RecStmt s

    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
class (VarPath s, Let s, RelPath (Lhs s)) => TupStmt s


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
class
  ( VarPath p, Tuple p, Extend p
  , Tuple (Group p), Member (Group p) ~ p, Member p ~ p
  ) => Patt p
  

-- | A program guaranteed to be a non-empty set of top level
--  recursive statements with an optional initial global import
class (RecStmt (Body r), Semigroup (Body r), Syntax (Rhs (Body r))) => Program r where
  type Body r
  
  prog_ :: Maybe Import -> Body r -> r
