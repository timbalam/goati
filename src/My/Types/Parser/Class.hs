{-# LANGUAGE FlexibleInstances, FlexibleContexts, RankNTypes, MultiParamTypeClasses, FunctionalDependencies, GeneralizedNewtypeDeriving #-}

-- | Final encoding of my language syntax
module My.Types.Parser.Class
  ( module My.Types.Parser
  , LitExpr(..), OpExpr(..), VarExpr(..), GroupExpr(..), Syntax
  , Field(..), Path(..)
  , DeclStmt(..), LetRecStmt(..), Rec
  , PunStmt(..), LetStmt(..), Ungroup(..), Tup, 
  , LetPathPatt(..), Patt
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
class Lit r where
  integerLit :: Integer -> r
  numberLit :: Double -> r
  stringLit :: StringExpr -> r
  
class Op r where
  unop :: Unop -> r -> r
  binop :: Binop -> r -> r -> r
  
class Local r where
  local :: Ident -> r
  
class Self r where
  self :: Key -> r
  
class Import r where
  import_ :: Import -> r
  
class Group r where
  group :: AGroup r -> r
  extend :: r -> AGroup r -> r
  
class Field r where
  at :: r -> Key -> r
  
  
-- | A path expression for my language recursively describes a set of
-- nested fields relative to a self- or environment-defined field
class (Local r, Field r) => LocalPath r
instance (Local r, Field r) => LocalPath r

class (Self r, Field r) => RelPath r
instance (Self r, Field r) => RelPath r

class (Local r, Self r, Field r) => VarPath r
instance (Local r, Self r, Field r) => VarPath r

  
-- | Combination of syntax features 
class (Lit r, Op r, VarPath r, Group r, Rec (Stmts r), Tup (Stmts r), Monoid (Stmts r r)) => Syntax r
instance (Lit r, Op r, VarPath r, Group r, Rec (Stmts r), Tup (Stmts r), Monoid (Stmts r r)) => Syntax r where



-- | Name groups
class Group g where
  tup :: ATup a -> g a
  block :: ABlock a -> g a
  
newtype ATup a = ATup (forall s . (Tup s, Monoid (s a)) => s a)
  deriving (Pun, Let)
  
newtype ABlock a = ABlock (forall s . (Rec s, Monoid (s a)) => s a)
  deriving (Decl, LetRec)
  
newtype AGroup a = AGroup (forall g . Group g => g a)
  deriving Group

-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
class Decl s where
  decl :: ARelPath -> s a
  
class LetRec s where
  letrec :: APatt -> a -> s a
  
class (Decl s, LetRec s) => Rec s
instance (Decl s, LetRec s) => Rec s

  
newtype ARelPath = ARelPath (forall r . RelPath r => r)
instance Self ARelPath where
  self x = ARelPath (self x)
  
instance Field ARelPath where
  ARelPath r `at` k = ARelPath (r `At` k)
  
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
class Pun s where
  pun :: AVarPath -> s a
  
class Let s where
  let_ :: ARelPath -> a -> s a
  
class (Pun s, Let s) => Tup s
instance (Pun s, Let s) => Tup s


newtype AVarPath = AVarPath (forall r . RelPath r => r)
  deriving (Local, Self, Field)


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
class LetPath p where
  letpath :: AVarPath -> p
  
class Ungroup p where
  ungroup :: ATup p -> p
  letungroup :: p -> ATup p -> p
  
class (LetPath p, Ungroup p) => Patt p
instance (LetPath p, Ungroup p) => Patt p
  
newtype APatt = APatt (forall p . Patt => p)
  deriving (LetPath, Ungroup)

{-
instance PathPatt Patt where
  pathSelf p = Patt (pathSelf p)
  pathEnv p = Patt (pathEnv p)
  
instance UngroupPatt Patt where
  ungroup tup = Patt (ungroup tup)
  pathungroup (Patt patt) tup = Patt (pathungroup patt tup)
-}

  
-- | A program guaranteed to be a non-empty set of top level
--  recursive statements with an optional initial global import
class (Local r, Self r) => Program r where
  program :: Maybe Import -> AProgBody r -> r
   

-- | Group with at least one recursive statement
newtype AProgBody a = AProgBody (forall s . (Rec s, Semigroup (s a)) => s a)
  deriving (Decl, LetRec)
