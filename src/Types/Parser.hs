{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Parser
  ( Expr(..)
  , Block(..)
  , RecStmt(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , SetExpr(..)
  , Ident
  , Path
  , Symbol(..)
  , Key(..)
  , Vis(..)
  , Var
  , VarPath
  , RelPath
  , Syntax
  , Tag
  , Free(..)
  , prec
  ) where
import qualified Data.Text as T
import Control.Monad.Free
import Control.Applicative( liftA2 )
import Control.Monad( ap )
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable

import Util
  

-- | Field label
type Ident = T.Text


-- | Symbol
newtype Symbol = S_ Ident
  deriving (Eq, Ord, Show)
  
  
-- | Field key
data Key a = Ident Ident | Symbol a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
  
  
-- | Aliases for parser
type Tag = Key Symbol
type Var = Vis Ident Tag
type Syntax = Expr Tag Var
type VarPath = Path Tag Var
type RelPath = Path Tag Tag
 
        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Field k a = a `At` k
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
instance Bifunctor Field where
  bimap f g (a `At` k) = g a `At` f k
  
instance Bifoldable Field where 
  bifoldMap f g (a `At` k) = g a `mappend` f k
  
instance Bitraversable Field where
  bitraverse f g (a `At` k) = liftA2 At (g a) (f k)
  
  
type Path k = Free (Field k)


-- | Binder visibility can be public or private to a scope
data Vis a b = Priv a | Pub b
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
  
  
instance Bifunctor Vis where
  bimap f g (Priv a) = Priv (f a)
  bimap f g (Pub b) = Pub (g b)
  
instance Bifoldable Vis where
  bifoldMap f g (Priv a) = f a
  bifoldMap f g (Pub b) = g b
  
instance Bitraversable Vis where
  bitraverse f g (Priv a) = Priv <$> f a
  bitraverse f g (Pub b) = Pub <$> g b
    
    
-- | High level syntax expression grammar for my-language
data Expr k a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var a
  | Get (Field k (Expr k a))
  | Block (Block k (Expr k a))
  | Extend (Expr k a) (Block k (Expr k a))
  | Unop Unop (Expr k a)
  | Binop Binop (Expr k a) (Expr k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  

instance Applicative (Expr k) where
  pure = return
  
  (<*>) = ap
  
instance Monad (Expr k) where
  return = Var
  
  e >>= f = go e where
    go (IntegerLit i) = IntegerLit i
    go (NumberLit d) = NumberLit d
    go (StringLit s) = StringLit s
    go (Var a) = f a
    go (Get (e `At` k)) = Get (go e `At` k)
    go (Block b) = Block (go <$> b)
    go (Extend e b) = Extend (go e) (go <$> b)
    go (Unop op e) = Unop op (go e)
    go (Binop op e w) = Binop op (go e) (go w)
  
  
instance Bifunctor Expr where
  bimap = bimapDefault
  
instance Bifoldable Expr where
  bifoldMap = bifoldMapDefault
  
instance Bitraversable Expr where
  bitraverse f g = go where
    go (IntegerLit i) = pure (IntegerLit i)
    go (NumberLit d) = pure (NumberLit d)
    go (StringLit s) = pure (StringLit s)
    go (Var a) = Var <$> g a
    go (Get (e `At` k)) = Get <$> liftA2 At (go e) (f k)
    go (Block b) = Block <$> bitraverse f go b
    go (Extend e b) = liftA2 Extend (go e) (bitraverse f go b)
    go (Unop op e) = Unop op <$> go e
    go (Binop op e w) = liftA2 (Binop op) (go e) (go w)

    
-- | Recursive and pattern (non-recursive) block types
data Block k a =
    Tup [Stmt k a]
  | Rec [RecStmt k a]
  deriving (Eq, Show, Functor, Foldable, Traversable)
  

instance Bifunctor Block where
  bimap = bimapDefault
  
instance Bifoldable Block where
  bifoldMap = bifoldMapDefault
  
instance Bitraversable Block where
  bitraverse f g (Tup xs) = Tup <$> traverse (bitraverse f g) xs
  bitraverse f g (Rec xs) = Rec <$> traverse (bitraverse f g) xs
    
  
-- | Literal strings are represented as non-empty lists of text
-- | TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show)
  
  
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
  deriving (Eq, Ord, Show)
  
  

-- a `prec` b is True if a has higher precedence than b
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


-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data RecStmt k a =
    DeclSym Symbol
  | DeclVar (Path k Ident) 
  | SetExpr k `SetRec` a
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
instance Bifunctor RecStmt where
  bimap = bimapDefault
  
instance Bifoldable RecStmt where
  bifoldMap = bifoldMapDefault
  
instance Bitraversable RecStmt where
  bitraverse f g = go where
    go (DeclSym s) = pure (DeclSym s)
    go (DeclVar p) = DeclVar <$> bitraverseFree f pure p
    go (e `SetRec` a) = liftA2 SetRec (traverse f e) (g a)
    
    
data Stmt k a =
    Pun (Path k (Vis Ident k))
  | Path k k `Set` a
  deriving (Eq, Show, Functor, Foldable, Traversable)
  

instance Bifunctor Stmt where
  bimap = bimapDefault
  
instance Bifoldable Stmt where
  bifoldMap = bifoldMapDefault
  
instance Bitraversable Stmt where
  bitraverse f g (Pun p) = Pun <$> bitraverseFree f (traverse f) p
  bitraverse f g (p `Set` a) = liftA2 Set (bitraverseFree f f p) (g a)


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr k =
    SetPath (Path k (Vis Ident k))
  | Decomp [Stmt k (SetExpr k)]
  | SetDecomp (SetExpr k) [Stmt k (SetExpr k)]
  deriving (Eq, Show)
  

instance Functor SetExpr where
  fmap = fmapDefault
  
instance Foldable SetExpr where
  foldMap = foldMapDefault
  
instance Traversable SetExpr where
  traverse f = go where
    go (SetPath p) = SetPath <$> bitraverseFree f (traverse f) p
    go (Decomp xs) = Decomp <$> traverse (bitraverse f go) xs
    go (SetDecomp e xs) = liftA2 SetDecomp (go e) (traverse (bitraverse f go) xs)
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
-- type MatchStmt = Stmt SetExpr
    

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
--type PathPattern = Path Tag


--newtype PatternExpr = PatternExpr (SetExpr PathPattern PatternExpr)
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
--type AsStmt = MatchStmt PathPattern PatternExpr
  
  
