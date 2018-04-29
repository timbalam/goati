{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies #-}

-- | Final encoding of my language syntax
--
-- A set of classes corresponding to particular syntactic language features
module My.Types.Syntax.Class
  ( module My.Types.Syntax
  , Syntax(..)
  , Local(..), Self(..), Extern(..), Field(..)
  , Tuple(..), Block(..)
  , Extend(..), Member
  , Let(..), RecStmt, TupStmt
  , Path, LocalPath, RelPath, VarPath, Patt
  , Program(..)
  
  -- dsl
  , not_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  ) where
import qualified Data.Text as T
import Data.Semigroup (Semigroup)
import Data.List.NonEmpty (NonEmpty)
import My.Types.Syntax
  ( Ident(..)
  , Key(..)
  , Import(..)
  , Unop(..)
  , Binop(..)
  , StringExpr
  )
  
infixl 9 #., #
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>
infixr 3 #&
infixr 2 #|
infixr 0 #=
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
class
  ( -- variables
    Local r, Self r, Extern r
    -- field access
  , Path r
    -- tuple and block expressions
  , Tuple r, Block r, Member r ~ r
    -- value extension using tuple and block expressions
  , Extend r, Tuple (Ext r), Block (Ext r), Member (Ext r) ~ r
  ) => Syntax r where
  
  -- literal forms
  int_ :: Integer -> r
  num_ :: Double -> r
  str_ :: StringExpr -> r
  
  -- unary and binary operators
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r
  
  
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=)
  :: Syntax a => a -> a -> a
not_ :: Syntax a => a -> a

(#&) = binop_ And
(#|) = binop_ Or
(#+) = binop_ Add
(#-) = binop_ Sub
(#*) = binop_ Prod
(#/) = binop_ Div
(#^) = binop_ Pow
(#==) = binop_ Eq
(#!=) = binop_ Ne
(#<) = binop_ Lt
(#<=) = binop_ Le
(#>) = binop_ Gt
(#>=) = binop_ Ge
  
not_ = unop_ Not

-- | Use a environment-bound name
class Local r where
  local_ :: Ident -> r
  
instance Local Ident where
  local_ = id
  
-- | Use a self-bound name
class Self r where
  self_ :: Key -> r
  
instance Self Key where
  self_ = id
  
-- | Use an external name
class Extern r where
  use_ :: Import -> r
  
instance Extern Import where
  use_ = id
  
-- | Use a name of a component of a compound type
class Field r where
  type Compound r
  
  (#.) :: Compound r -> Key -> r

  
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
  type Ext r
  
  (#) :: r -> Ext r -> r
  
-- | Assignment
class Let s where
  type Lhs s
  type Rhs s
  
  (#=) :: Lhs s -> Rhs s -> s


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


-- | Path of nested field accesses to a self-bound or env-bound value
class (Field p, Compound p ~ p) => Path p
class (Self p, Field p, Self (Compound p), Path (Compound p)) => RelPath p
class (Local p, Field p, Local (Compound p), Path (Compound p)) => LocalPath p
class (LocalPath p, RelPath p) => VarPath p

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
class
  ( VarPath p, Tuple p, Member p ~ p
  , Extend p, Tuple (Ext p), Member (Ext p) ~ p
  ) => Patt p
  

-- | A program guaranteed to be a non-empty set of top level
--  recursive statements with an optional initial global import
class (RecStmt (Body r), Semigroup (Body r)) => Program r where
  type Body r
  
  prog_ :: Maybe Import -> Body r -> r
  
  
-- | Lift classes through lists and non-emptys
instance Self a => Self [a] where
  self_ = pure . self_
  
instance Local a => Local [a] where
  local_ = pure . local_
  
instance Field a => Field [a] where
  type Compound [a] = Compound a
  
  x #. k = [x #. k]
  
instance LocalPath a => LocalPath [a]

instance RelPath a => RelPath [a]
  
instance VarPath a => VarPath [a]

instance Let a => Let [a] where
  type Lhs [a] = Lhs a
  type Rhs [a] = Rhs a
  
  l #= r = [l #= r]
  
instance TupStmt a => TupStmt [a]

instance RecStmt a => RecStmt [a]

-- | Lift classes through lists and non-emptys
instance Self a => Self (NonEmpty a) where
  self_ = pure . self_
  
instance Local a => Local (NonEmpty a) where
  local_ = pure . local_
  
instance Field a => Field (NonEmpty a) where
  type Compound (NonEmpty a) = Compound a
  
  x #. k = pure (x #. k)
  
instance LocalPath a => LocalPath (NonEmpty a)

instance RelPath a => RelPath (NonEmpty a)
  
instance VarPath a => VarPath (NonEmpty a)

instance Let a => Let (NonEmpty a) where
  type Lhs (NonEmpty a) = Lhs a
  type Rhs (NonEmpty a) = Rhs a
  
  l #= r = pure (l #= r)
  
instance TupStmt a => TupStmt (NonEmpty a)

instance RecStmt a => RecStmt (NonEmpty a)
