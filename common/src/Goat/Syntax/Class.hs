{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable, ConstraintKinds, GeneralizedNewtypeDeriving #-}

-- | This module contains a set of typeclasses encoding syntactic features of Goat
-- (often called a 'final encoding').
-- The classes describe how an syntactic feature is interpreted by an implementation. 
-- See 'Goat.Types.Expr' and 'Goat.Types.Eval' for the internal implementations used by this interpreter.
-- See 'Goat.Syntax.Parser' for a parser for the textual representation.
module Goat.Syntax.Class
  ( Ident(..)
  , Unop(..), Binop(..), prec
  , ArithB_(..), LogicB_(..), CmpB_(..)
  , ArithU_(..), LogicU_(..)
  , Text_(..)
  , Local(..), Self(..), Extern_(..), Field_(..)
  , Block(..), Extend_(..), Let(..), Esc(..)
  , Include(..), Module(..), Imports(..)
  
  -- synonyms
  , Field, Extern, Lit, Extend
  , Expr, Path, RelPath, LocalPath, ExtendBlock
  , Patt, Decl, Pun, LetMatch, Rec
  , LetPatt, Preface, LetImport
  
  -- dsl
  --, not_
  --, neg_
  --, (#&&), (#||)
  --, (#+), (#-), (#*), (#/), (#^)
  --, (#==), (#!=), (#<), (#<=), (#>), (#>=)
  ) where
  
import Goat.Syntax.Ident (Ident(..))
import Goat.Syntax.Field (Field_(..))
--import Goat.Syntax.Symbol (Symbol(..))
import Goat.Syntax.Unop (ArithU_(..), LogicU_(..))
import Goat.Syntax.Binop
  (CmpB_(..), ArithB_(..), LogicB_(..))
import Goat.Syntax.Extern (Extern_(..))
import Goat.Syntax.Extend (Extend_(..))
import Goat.Syntax.Text (Text_(..))
import Control.Applicative (liftA2)
import Data.Biapplicative (Biapplicative(..), Bifunctor(..), biliftA2)
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Typeable (Typeable)


--infixl 9 #
--infixr 8 #^
--infixl 7 #*, #/
--infixl 6 #+, #-
--infix 4 #==, #!=, #<, #<=, #>=, #>
--infixr 3 #&&
--infixr 2 #||
infixr 1 #=


-- | Alias
type Field = Field_
type Extern = Extern_
type Extend = Extend_
    
-- | High level syntax expression grammar for my language
--
-- This expression form closely represents the textual form of my language.
-- After import resolution, it is checked and lowered and interpreted in a
-- core expression form.
type Expr r =
  ( Path r
  , Lit r
  , Esc r, Lower r ~ r
  , Local r
  , Self r
  , Extern r
  , ExtendBlock r
  , Rec (Stmt r), Rhs (Stmt r) ~ r
  )
  
type Rec s = (Decl s, LetPatt s, Pun s)
  

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
type Lit r =
  ( IsString r, Fractional r
  , LogicB_ r, ArithB_ r, CmpB_ r
  , LogicU_ r, ArithU_ r
  )
{-
class (Num r, IsString r, Fractional r) => Lit r where
  -- unary and binary operators
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r

  
(#&&), (#||), (#+), (#-), (#*), (#/), (#^),
  (#==), (#!=), (#<), (#<=), (#>), (#>=)
  :: Lit a => a -> a -> a
not_, neg_ :: Lit a => a -> a

(#&&) = binop_ And
(#||) = binop_ Or
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
-}

-- | Use a environment-bound name
class Local r where local_ :: Ident -> r
  
instance Local Ident where local_ = id
  
-- | Use a self-bound name
class Self r where self_ :: Ident -> r
  
instance Self Ident where self_ = id
  
-- | Use an external name
--class Extern r where use_ :: Ident -> r

--instance Extern Ident where use_ = id
  
-- | Nested field accesses
type Path r = (Field r, Compound r ~ r)

-- | Local path
type LocalPath r = (Local r, Field r, Local (Compound r), Path (Compound r))

-- | Relative path
type RelPath r = (Self r, Field r, Self (Compound r), Path (Compound r))

-- | Lift an expression to a higher scope
class Esc r where
  type Lower r
  esc_ :: Lower r -> r
  
-- | Construct a block
class Block r where
  type Stmt r
  block_ :: [Stmt r] -> r
  
-- | Assignment
class Let s where
  type Lhs s
  type Rhs s
  (#=) :: Lhs s -> Rhs s -> s
  
-- | Declare statement (declare a path without a value)
type Decl s = RelPath s

-- | Pun statement (define a path to equal the equivalent path in scope/ match
-- a path to an equivalent leaf pattern)
type Pun s = (Esc s, RelPath (Lower s), LocalPath (Lower s))

-- | Let statement (define a path to be equal to a value / match a path to
-- a pattern)
type LetMatch s = (Let s, RelPath (Lhs s), Esc (Rhs s))

-- | Let pattern statement (define a pattern to be equal to a value)
type LetPatt s = (Let s, Patt (Lhs s))

-- | Extend a value with a new name group
{-
class Extend r where
  type Ext r
  (#) :: r -> Ext r -> r
-}
  
-- | Create or extend a value with a literal block
type ExtendBlock r =
  ( Block r, Extend r, Block (Ext r), Stmt (Ext r) ~ Stmt r )

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
-- * Let path pattern (leaf pattern assigns matched value to path)
-- * Block pattern (matches a set of paths to nested (lifted) patterns)
-- * An block pattern with left over pattern (matches set of fields not
--   matched by the block pattern)
type Patt p =
  ( LocalPath p, RelPath p, ExtendBlock p
  , Pun (Stmt p), LetMatch (Stmt p)
  , Lower (Rhs (Stmt p)) ~ p
  )

-- | Module preface can include
-- * an '@import' section with a list of external imports 
-- * an '@include' section with a fall-back module name
-- * an '@module' section with the main module code
type Preface r =
  ( Module r, Include r, Module (Inc r)
  , ModuleStmt (Inc r) ~ ModuleStmt r
  , Imports r, Module (Imp r), ModuleStmt (Imp r) ~ ModuleStmt r
  , Include (Imp r), Inc (Imp r) ~ Inc r
  , Module (Inc (Imp r))
  )

-- | Mapping of '@use' names to external module files
class Imports r where
  type ImportStmt r
  type Imp r
  extern_ :: [ImportStmt r] -> Imp r -> r
  
  
-- | Import statement (map identifier to a path string)
type LetImport s = (Let s, Local (Lhs s), IsString (Rhs s))
  
  
-- | Fall-back module name
class Include r where
  type Inc r
  include_ :: Ident -> Inc r -> r
  
  
-- | Main module code
class Module r where
  type ModuleStmt r
  module_ :: [ModuleStmt r] -> r
