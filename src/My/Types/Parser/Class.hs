{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, RankNTypes, TypeFamilies, GeneralizedNewtypeDeriving #-}

-- | Final encoding of my language syntax
module My.Types.Parser.Class
  ( module My.Types.Parser
  , Lit(..), Op(..)
  , Tuple(..), Block(..), Group
  , ATup(..), ABlock(..), Syntax
  , Local(..), Self(..), Extern(..), Field(..), Path(..)
  , AVarPath(..), ARelPath(..)
  , Stmts(..), AGroup
  , Decl(..), LetRec(..), ABlock(..), Rec
  , PunStmt(..), LetStmt(..), ATup(..), Tup
  , LetPath(..), Ungroup(..), APatt(..), Patt
  , Program(..), AProgBody
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
  
-- | A path expression for my language recursively describes a set of
-- nested fields relative to a self- or environment-defined field
class Local r where
  local :: Ident -> r
  
class Self r where
  self :: Key -> r
  
class Extern r where
  import_ :: Import -> r
  
class Field r where
  at :: r -> Key -> r
  
class (Local r, Field r) => LocalPath r
instance (Local r, Field r) => LocalPath r

class (Self r, Field r) => RelPath r
instance (Self r, Field r) => RelPath r

class (Local r, Self r, Field r) => VarPath r
instance (Local r, Self r, Field r) => VarPath r


newtype ARelPath = ARelPath (forall r . RelPath r => r)
instance Self ARelPath where
  self x = ARelPath (self x)
  
instance Field ARelPath where
  ARelPath r `at` k = ARelPath (r `at` k)

newtype AVarPath = AVarPath (forall r . VarPath r => r)
instance Local AVarPath where
  local x = AVarPath (local x)
  
instance Self AVarPath where
  self x = AVarPath (self x)
  
instance Field AVarPath where
  at (AVarPath r) x = AVarPath (at r x)
  
  
-- | The type of a value assigned in a name group
type family Member r

class Tuple r where
  tup :: ATup (Member r) -> r
  
class Block r where
  block :: ABlock (Member r) -> r
  
class Extend r where
  type Group r
  
  extend :: r -> Group r -> r

  
-- | Combination of syntax features 
class (Lit r, Op r, VarPath r, Tuple r, Block r, Tuple (Group r), Block (Group r), Extend r, Member r ~ r) => Syntax r
instance (Lit r, Op r, VarPath r, Tuple r, Block r, Tuple (Group r), Block (Group r), Extend r, Member r ~ r) => Syntax r


-- | Statements in a recursive group expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
class Decl s where
  decl :: ARelPath -> s a
  
class Let s where
  type Lhs s
  
  let_ :: Lhs s -> a -> s a
  
class (Decl s, Let s, Patt (Lhs s)) => Rec s
instance Rec s
  
newtype ABlock a = ABlock (forall s . (Rec s, Monoid (s a)) => s a)

  
    
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
  
class (Pun s, Let s, RelPath (Lhs s)) => Tup s
instance Tup s


newtype ATup a = ATup (forall s . (Tup s, Monoid (s a)) => s a)


-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Ungroup pattern (matches a set of paths to corresponding nested patterns)
--   * An ungroup pattern with left over pattern (matches set of fields not
--      matched by the ungroup pattern)
class (VarPath p, Tuple p, p ~ Member p, Extend p, Tuple (Group p), p ~ Group p) => Patt p
instance Patt p
  
newtype APatt = APatt (forall p . Patt p => p)
instance Local APatt where
  local p = APatt (local p)
  

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
instance Decl AProgBody where
  decl p = AProgBody (decl p)
  
instance Let AProgBody where
  let_ p a = AProgBody (let_ p a)
