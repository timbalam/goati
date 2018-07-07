{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, ConstraintKinds #-}

-- | Final encoding of my language syntax
--
-- A set of classes corresponding to particular syntactic language features
module My.Types.Syntax.Class
  ( module My.Types.Syntax
  , Feat(..), Expr(..), Defns(..), Lit(..), Syntax(..)
  , Local(..), Self(..), Extern(..), Field(..)
  , Tuple(..), Block(..)
  , Extend(..), Member, Sep(..), Splus(..)
  , Let(..), RecStmt, TupStmt
  , Path, LocalPath, RelPath, VarPath, Patt
  , Global(..)
  
  -- dsl
  , not_, neg_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  ) where
import qualified Data.Text as T
import Data.String (IsString)
import My.Types.Syntax
  ( Ident(..)
  , Key(..)
  , Import(..)
  , Unop(..)
  , Binop(..)
  )
  
infixl 9 #., #
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>
infixr 3 #&
infixr 2 #|
infixr 1 #=, #...
infixr 0 #:
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
type Syntax r = (Expr r, Extern r)
type Expr r = (Feat r, Member r ~ r)

-- | Core expression features of component accesses, literals, name group definitions
-- and extensions, name usages
type Feat r = (Path r, Defns r, Lit r, Local r, Self r)
  

-- | Literal and value extending tuple and block expressions
type Defns r = 
  ( Tuple r, Block r
  , Extend r, Tuple (Ext r), Block (Ext r), Member (Ext r) ~ Member r
  , Tup r ~ Tup (Ext r), Rec r ~ Rec (Ext r)
  )
  
  
-- | Extend an expression with literal forms
class (Num r, IsString r, Fractional r) => Lit r where
  -- unary and binary operators
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r

  
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=)
  :: Lit a => a -> a -> a
not_, neg_ :: Lit a => a -> a

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
neg_ = unop_ Neg

-- | Use a environment-bound name
class Local r where
  local_ :: Ident -> r
  
instance Local Ident where
  local_ = id
  
-- | Use a self-bound name
class Self r where
  self_ :: Ident -> r
  
instance Self Key where
  self_ = K_
  
-- | Use an external name
class Extern r where
  use_ :: Ident -> r
  
instance Extern Import where
  use_ = Use
  
-- | Use a name of a component of a compound type
class Field r where
  type Compound r
  
  (#.) :: Compound r -> Ident -> r
  
-- | Path of nested field accesses to a self-bound or env-bound value
type Path p = (Field p, Compound p ~ p)
type RelPath p = (Self p, Field p, Self (Compound p), Path (Compound p))
type LocalPath p = (Local p, Field p, Local (Compound p), Path (Compound p))
type VarPath p = (LocalPath p, RelPath p)

-- | A value assignable in a name group
type family Member r

-- | Sequence of statements
class Sep r where
  (#:) :: r -> r -> r
  
-- | Empty statement
class Sep r => Splus r where
  empty_ :: r
  
-- | Construct a tuple
class (TupStmt (Tup r), Splus (Tup r), Rhs (Tup r) ~ Member r) => Tuple r where
  type Tup r
  
  tup_ :: Tup r -> r
  
-- | Construct a block
class (RecStmt (Rec r), Splus (Rec r), Rhs (Rec r) ~ Member r) => Block r where
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
type RecStmt s = (RelPath s, Let s, Patt (Lhs s))
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
type TupStmt s = (VarPath s, Let s, RelPath (Lhs s))

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
type Patt p =
  ( VarPath p, Tuple p, Member p ~ p
  , Extend p, Tuple (Ext p)
  , Tup p ~ Tup (Ext p), Member p ~ Member (Ext p)
  )
  

-- | A program guaranteed to be a non-empty set of top level recursive statements 
-- with an initial global import
class (RecStmt (Body r), Sep (Body r), Rhs (Body r) ~ Member r, Syntax (Member r), Extern (Prelude r)) => Global r where
  type Body r
  type Prelude r
  
  (#...) :: Prelude r -> Body r -> r
 

