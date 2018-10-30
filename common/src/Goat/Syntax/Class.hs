{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, ConstraintKinds, GeneralizedNewtypeDeriving #-}

-- | This module contains a set of typeclasses encoding syntactic features of Goat
-- (often called a 'final encoding').
-- The classes describe how an syntactic feature is interpreted by an implementation. 
-- See 'Goat.Types.Expr' and 'Goat.Types.Eval' for the internal implementations used by this interpreter.
-- See 'Goat.Syntax.Parser' for a parser for the textual representation.
module Goat.Syntax.Class
  ( Ident(..), Unop(..), Binop(..), prec
  , Lit(..), Local(..), Self(..), Extern(..), Field(..)
  , Block(..), Extend(..), Let(..)
  
  -- dsl
  , not_, neg_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  ) where
import Control.Applicative (liftA2)
import Data.Biapplicative (Biapplicative(..), Bifunctor(..), biliftA2)
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Typeable (Typeable)
  
infixl 9 #., #
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>
infixr 3 #&
infixr 2 #|
infixr 1 #=, #:
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
--type Syntax r = (Expr r, Extern r)
--type Expr r = (Feat r, Rhs (Rec r) ~ r)

-- | Core expression features of component accesses, literals, name group definitions
-- and extensions, name usages
--type Feat r = (Path r, Defns r, Lit r, Local r, Self r)
  

-- | Literal and value extending tuple and block expressions
--type Defns r = 
--  ( Tuple r, Block r, Value (Tup r) ~ Rhs (Rec r)
--  , Extend r, Tuple (Ext r), Block (Ext r)
--  , Tup r ~ Tup (Ext r), Rec r ~ Rec (Ext r)
--  )
  
  
-- | Unary operators
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Binary operators
data Binop =
    Add
  | Sub
  | Prod
  | Div
  | Pow
  | And
  | Or
  | Lt
  | Gt 
  | Eq
  | Ne
  | Le
  | Ge
  deriving (Eq, Ord, Show, Typeable)
  
  

-- | a `prec` b is True if a has higher precedence than b
--
-- TODO: Implement relative precedence??
prec :: Binop -> Binop -> Bool
prec _    Pow   = False
prec Pow  _     = True
prec _    Prod  = False
prec _    Div   = False
prec Prod _     = True
prec Div  _     = True
prec _    Add   = False
prec _    Sub   = False
prec Add  _     = True
prec Sub  _     = True
prec _    Eq    = False
prec _    Ne    = False
prec _    Lt    = False
prec _    Gt    = False
prec _    Le    = False
prec _    Ge    = False
prec Eq   _     = True
prec Ne   _     = True
prec Lt   _     = True
prec Gt   _     = True
prec Le   _     = True
prec Ge   _     = True
prec _    And   = False
prec And  _     = True
prec _    Or    = False
--prec Or   _     = True
  
  
  
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


-- | Identifier
newtype Ident = I_ T.Text deriving (Eq, Ord, Show, Typeable)
  
instance IsString Ident where fromString = I_ . T.pack

-- | Use a environment-bound name
class Local r where local_ :: Ident -> r
  
instance Local Ident where local_ = id
  
-- | Use a self-bound name
class Self r where self_ :: Ident -> r
  
instance Self Ident where self_ = id
  
-- | Use an external name
class Extern r where use_ :: Ident -> r
  
-- | Use a name of a component of a compound type
class Field p q | q -> p where
  (#.) :: p -> Ident -> q
  
-- | Construct a block
class Block s r | r -> stmt where
  block_ :: [s] -> r
  
-- | Extend a value with a new name group
class Extend ext r | r -> ext where
  (#) :: r -> ext -> r
  
-- | Assignment
class Let lhs rhs s | s -> lhs rhs where
  (#=) :: lhs -> rhs -> s

-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
--type RecStmt s = (RelPath s, Let s, Patt (Lhs s))
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
--type TupStmt s = (VarPath s, Assoc s, RelPath (Label s))

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
--type Patt p =
--  ( VarPath p, Tuple p, Value (Tup p) ~ p
--  , Extend p, Tuple (Ext p)
--  , Tup p ~ Tup (Ext p)
--  )