{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, GeneralizedNewtypeDeriving #-}

-- | Final encoding of my language syntax
--
-- A set of classes corresponding to particular syntactic language features
module My.Types.Syntax.Class
  ( module My.Types.Syntax
  , Expr(..), Syntax(..)
  , Local(..), Self(..), Extern(..), Field(..)
  , Tuple(..), Block(..)
  , Extend(..), Member
  , Let(..), RecStmt, TupStmt
  , Path, LocalPath, RelPath, VarPath, Patt
  , Global(..)
  
  -- higher order
  , S(..), Local1(..), Self1(..), Field1(..)
  , LocalPath1(..), RelPath1(..), VarPath1(..)
  
  -- dsl
  , not_
  , (#&), (#|)
  , (#+), (#-), (#*), (#/), (#^)
  , (#==), (#!=), (#<), (#<=), (#>), (#>=)
  ) where
import qualified Data.Text as T
import Data.Semigroup (Semigroup)
import Data.List.NonEmpty (NonEmpty)
import Control.Applicative (liftA2)
import Data.Functor.Alt (Alt)
import Data.Functor.Plus (Plus)
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
infixr 0 #=, #...
    
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form. See 'Types/Expr.hs'.
class (Expr r, Local r, Self r, Extern r) => Syntax r

class
  ( -- field access
    Path r
    -- tuple and block expressions
  , Tuple r, Block r, Member r ~ r
    -- value extension using tuple and block expressions
  , Extend r, Tuple (Ext r), Block (Ext r), Member (Ext r) ~ r
  ) => Expr r where
  
  -- literal forms
  int_ :: Integer -> r
  num_ :: Double -> r
  str_ :: StringExpr -> r
  
  -- unary and binary operators
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r

  
  
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=)
  :: Expr a => a -> a -> a
not_ :: Expr a => a -> a

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
  
class Local1 s where
  local1_ :: Ident -> s a
  
newtype S s a = S { getS :: s a }
  deriving (Monoid, Semigroup)
  
instance Local1 s => Local (S s a) where
  local_ = S . local1_
  
-- | Use a self-bound name
class Self r where
  self_ :: Key -> r
  
instance Self Key where
  self_ = id
  
class Self1 s where
  self1_ :: Key -> s a
  
instance Self1 s => Self (S s a) where
  self_ = S . self1_
  
-- | Use an external name
class Extern r where
  use_ :: Import -> r
  
instance Extern Import where
  use_ = id
  
-- | Use a name of a component of a compound type
class Field r where
  type Compound r
  
  (#.) :: Compound r -> Key -> r
  
class Field1 (s :: * -> *) where
  type Compound1 s
  
  at1_ :: Compound1 s -> Key -> s a
  
instance Field1 s => Field (S s a) where
  type Compound (S s a) = Compound1 s
  
  s #. k = S (at1_ s k)
  
-- | Path of nested field accesses to a self-bound or env-bound value
class (Field p, Compound p ~ p) => Path p
class (Self p, Field p, Self (Compound p), Path (Compound p)) => RelPath p
class (Local p, Field p, Local (Compound p), Path (Compound p)) => LocalPath p
class (LocalPath p, RelPath p) => VarPath p

class (Self1 s, Field1 s, Self (Compound1 s), Path (Compound1 s)) => RelPath1 s
class (Local1 s, Field1 s, Local (Compound1 s), Path (Compound1 s)) => LocalPath1 s
class (LocalPath1 s, RelPath1 s) => VarPath1 s

instance RelPath1 s => RelPath (S s a)
instance LocalPath1 s => LocalPath (S s a)
instance VarPath1 s => VarPath (S s a)

-- | A value assignable in a name group
type family Member r
  
-- | Construct a tuple
class (TupStmt (Tup r), Plus (Tup r)) => Tuple r where
  type Tup r :: * -> *
  
  tup_ :: S (Tup r) (Member r) -> r
  
-- | Construct a block
class (RecStmt (Rec r), Plus (Rec r)) => Block r where
  type Rec r :: * -> *
  
  block_ :: S (Rec r) (Member r) -> r
  
-- | Extend a value with a new name group
class Extend r where
  type Ext r
  
  (#) :: r -> Ext r -> r
  
-- | Assignment
class Let s where
  type Lhs s
  
  (#=) :: Lhs s -> a -> s a
  
instance Let s => Let (S s) where
  type Lhs (S s) = Lhs s
  
  l #= r = S (l #= r)


-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
class (RelPath1 s, Let s, Patt (Lhs s)) => RecStmt s

    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
class (VarPath1 s, Let s, RelPath (Lhs s)) => TupStmt s

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
  

-- | A program guaranteed to be a non-empty set of top level recursive statements
-- with an initial global import
class (RecStmt (Body r), Alt (Body r), Syntax (Member r)) => Global r where
  type Body r :: * -> *
  
  (#...) :: Import -> Body r (Member r) -> r
 

