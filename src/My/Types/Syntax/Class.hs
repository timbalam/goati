{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, ConstraintKinds, GeneralizedNewtypeDeriving #-}

-- | Final encoding of my language syntax
--
-- A set of classes corresponding to particular syntactic language features
module My.Types.Syntax.Class
  ( Ident(..), Unop(..), Binop(..), prec
  , Feat, Expr, Defns, Syntax
  , Lit(..), Local(..), Self(..), Extern(..), Field(..)
  , Tuple(..), Block(..)
  , Extend(..), Member, Sep(..), Splus(..)
  , Let(..), RecStmt, TupStmt, Patt
  , Path, LocalPath, RelPath, VarPath
  , Global(..)
  
  -- wrappers
  , Sbi(..), Sap(..)
  
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
newtype Ident = I_ T.Text
  deriving (Eq, Ord, Show, Typeable)
  
instance IsString Ident where
  fromString = I_ . T.pack

-- | Use a environment-bound name
class Local r where
  local_ :: Ident -> r
  
instance Local Ident where
  local_ = id
  
-- | Use a self-bound name
class Self r where
  self_ :: Ident -> r
  
instance Self Ident where
  self_ = id
  
-- | Use an external name
class Extern r where
  use_ :: Ident -> r
  
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
 

-- | Useful types
newtype Sap f a = Sap (f a) deriving (Functor, Applicative)
newtype Sbi p a b = Sbi (p a b)

instance Bifunctor p => Bifunctor (Sbi p) where
  bimap f g (Sbi p) = Sbi (bimap f g p)
  
instance Biapplicative p => Biapplicative (Sbi p) where
  bipure a b = Sbi (bipure a b)
  Sbi pf <<*>> Sbi pa = Sbi (pf <<*>> pa)
  
instance (IsString a, Applicative f) => IsString (Sap f a) where
  fromString = pure . fromString
instance (IsString a, IsString b, Biapplicative p) => IsString (Sbi p a b) where
  fromString t = bipure (fromString t) (fromString t)
  
instance (Fractional a, Applicative f) => Fractional (Sap f a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)
instance (Fractional a, Fractional b, Biapplicative p) => Fractional (Sbi p a b) where
  fromRational n = bipure (fromRational n) (fromRational n)
  (/) = biliftA2 (/) (/)

instance (Num a, Applicative f) => Num (Sap f a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  abs = fmap abs
  signum = fmap signum
  negate = fmap negate
instance (Num a, Num b, Biapplicative p) => Num (Sbi p a b) where
  fromInteger i = bipure (fromInteger i) (fromInteger i)
  (+) = biliftA2 (+) (+)
  (-) = biliftA2 (-) (-)
  (*) = biliftA2 (*) (*)
  abs = bimap abs abs
  signum = bimap signum signum
  negate = bimap negate negate

instance (Lit a, Applicative f) => Lit (Sap f a) where
  unop_ op = fmap (unop_ op)
  binop_ op = liftA2 (binop_ op)
instance (Lit a, Lit b, Biapplicative p) => Lit (Sbi p a b) where
  unop_ op = bimap (unop_ op) (unop_ op)
  binop_ op = biliftA2 (binop_ op) (binop_ op)

instance (Local a, Applicative f) => Local (Sap f a) where
  local_ = pure . local_
instance (Local a, Local b, Biapplicative p) => Local (Sbi p a b) where
  local_ i = bipure (local_ i) (local_ i)

instance (Self a, Applicative f) => Self (Sap f a) where
  self_ = pure . self_ 
instance (Self a, Self b, Biapplicative p) => Self (Sbi p a b) where
  self_ i = bipure (self_ i) (self_ i)

instance (Extern a, Applicative f) => Extern (Sap f a) where
  use_ = pure . use_
instance (Extern a, Extern b, Biapplicative p) => Extern (Sbi p a b) where
  use_ i = bipure (use_ i) (use_ i)

instance (Field a, Applicative f) => Field (Sap f a) where
  type Compound (Sap f a) = Sap f (Compound a)
  f #. k = fmap (#. k) f
instance (Field a, Field b, Bifunctor p) => Field (Sbi p a b) where
  type Compound (Sbi p a b) = Sbi p (Compound a) (Compound b)
  p #. k = bimap (#. k) (#. k) p

type instance Member (Sap f a) = Sap f (Member a)
type instance Member (Sbi p a b) = Sbi p (Member a) (Member b)

instance (Sep a, Applicative f) => Sep (Sap f a) where
  (#:) = liftA2 (#:)
instance (Sep a, Sep b, Biapplicative p) => Sep (Sbi p a b) where
  (#:) = biliftA2 (#:) (#:)
  
instance (Splus a, Applicative f) => Splus (Sap f a) where
  empty_ = pure empty_
instance (Splus a, Splus b, Biapplicative p) => Splus (Sbi p a b) where
  empty_ = bipure empty_ empty_

instance (Tuple a, Applicative f) => Tuple (Sap f a) where
  type Tup (Sap f a) = Sap f (Tup a)
  tup_ = fmap tup_
instance (Tuple a, Tuple b, Biapplicative p) => Tuple (Sbi p a b) where
  type Tup (Sbi p a b) = Sbi p (Tup a) (Tup b)
  tup_ = bimap tup_ tup_

instance (Block a, Applicative f) => Block (Sap f a ) where
  type Rec (Sap f a) = Sap f (Rec a)
  block_ = fmap block_
instance (Block a, Block b, Biapplicative p) => Block (Sbi p a b) where
  type Rec (Sbi p a b) = Sbi p (Rec a) (Rec b)
  block_ = bimap block_ block_
  
instance (Extend a, Applicative f) => Extend (Sap f a) where
  type Ext (Sap f a) = Sap f (Ext a)
  (#) = liftA2 (#)
instance (Extend a, Extend b, Biapplicative p) => Extend (Sbi p a b) where
  type Ext (Sbi p a b) = Sbi p (Ext a) (Ext b)
  (#) = biliftA2 (#) (#)

instance (Let a, Applicative f) => Let (Sap f a) where
  type Lhs (Sap f a) = Sap f (Lhs a)
  type Rhs (Sap f a) = Sap f (Rhs a)
  (#=) = liftA2 (#=)
instance (Let a, Let b, Biapplicative p) => Let (Sbi p a b) where
  type Lhs (Sbi p a b) = Sbi p (Lhs a) (Lhs b)
  type Rhs (Sbi p a b) = Sbi p (Rhs a) (Rhs b)
  (#=) = biliftA2 (#=) (#=)

instance (Global a, Applicative f) => Global (Sap f a) where
  type Body (Sap f a) = Sap f (Body a)
  type Prelude (Sap f a) = Sap f (Prelude a)
  (#...) = liftA2 (#...)
instance (Global a, Global b, Biapplicative p) => Global (Sbi p a b) where
  type Body (Sbi p a b) = Sbi p (Body a) (Body b)
  type Prelude (Sbi p a b) = Sbi p (Prelude a) (Prelude b)
  (#...) = biliftA2 (#...) (#...)

