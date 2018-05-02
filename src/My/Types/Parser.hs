{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, TypeFamilies #-}

-- | Types of my language syntax
module My.Types.Parser
  ( Expr(..)
  , Group(..)
  , RecStmt(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Field(..)
  , Patt(..)
  , Program(..)
  , Ident(..)
  , Key(..)
  , StringExpr
  , Path
  , Import(..)
  , Vis(..)
  , Res(..)
  , Name
  , VarPath
  , Free(..)
  , prec
  ) where
import qualified Data.Text as T
import Control.Monad.Free
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
import Data.List.NonEmpty (NonEmpty)
import Data.String (IsString(..))
import Data.Semigroup (First(..))
import Data.Functor.Alt (Alt(..))
import Data.Functor.Plus (Plus(..))
--import Data.Void (Void)
import My.Util
import qualified My.Types.Syntax.Class as S
import My.Types.Syntax
  
  
-- | Alias for typical variable name type
type Name a b = Res (Vis a b)


-- | Alias for typical set target type
type VarPath = Vis (Path Ident) (Path Key)
 
 
-- | A path expression for my language recursively describes a set of nested
--   fields relative to a self- or environment-defined field
type Path = Free Field

data Field a = a `At` Key
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance S.Field (Free Field a) where
  type Compound (Free Field a) = Free Field a
  
  p #. k = Free (p `At` k)

instance S.Path (Free Field a)

instance S.Local a => S.Local (Free Field a) where
  local_ = Pure . S.local_
  
instance S.Self a => S.Self (Free Field a) where
  self_ = Pure . S.self_
  
instance S.Local a => S.LocalPath (Free Field a)

instance S.Self a => S.RelPath (Free Field a)

instance (S.Local a, S.Self a) => S.VarPath (Free Field a)


-- | Binder visibility can be public or private to a scope
data Vis a b = Priv a | Pub b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)
  
instance Bifunctor Vis where
  bimap f g (Priv a) = Priv (f a)
  bimap f g (Pub b) = Pub (g b)
  
instance Bifoldable Vis where
  bifoldMap f g (Priv a) = f a
  bifoldMap f g (Pub b) = g b
  
instance Bitraversable Vis where
  bitraverse f g (Priv a) = Priv <$> f a
  bitraverse f g (Pub b) = Pub <$> g b
  
instance S.Local a => S.Local (Vis a b) where
  local_ = Priv . S.local_
  
instance S.Self b => S.Self (Vis a b) where
  self_ = Pub . S.self_
  
instance (S.Field a, S.Field b) => S.Field (Vis a b) where
  type Compound (Vis a b) = Vis (S.Compound a) (S.Compound b)
  
  p #. k = bimap (S.#. k) (S.#. k) p
  
instance (S.Path a, S.Path b) => S.Path (Vis a b)
  
  
-- | .. or internal or external to a file
data Res a b = In a | Ex b
  deriving (Eq, Ord, Show, Typeable, Functor, Foldable, Traversable)

instance Bifunctor Res where
  bimap f g (In a) = In (f a)
  bimap f g (Ex b) = Ex (g b)

instance Bifoldable Res where
  bifoldMap f g (In a) = f a
  bifoldMap f g (Ex b) = g b

instance Bitraversable Res where
  bitraverse f g (In a) = In <$> f a
  bitraverse f g (Ex b) = Ex <$> g b
  
instance S.Local a => S.Local (Res a b) where
  local_ = In . S.local_ 
  
instance S.Self a => S.Self (Res a b) where
  self_ = In . S.self_
  
instance S.Extern b => S.Extern (Res a b) where
  use_ = Ex . S.use_
    
    
-- | High level syntax expression grammar for my language
--
--   This expression form closely represents the textual form of my language.
--   After import resolution, it is checked and lowered and interpreted in a
--   core expression form. See 'Types/Expr.hs'.
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | Var a
  | Get (Field (Expr a))
  | Group (Group (Expr a))
  | Extend (Expr a) (Group (Expr a))
  | Unop Unop (Expr a)
  | Binop Binop (Expr a) (Expr a)
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  e >>= f = go e where
    go (IntegerLit i) = IntegerLit i
    go (NumberLit d) = NumberLit d
    go (StringLit s) = StringLit s
    go (Var a) = f a
    go (Get (e `At` k)) = Get (go e `At` k)
    go (Group b) = Group (go <$> b)
    go (Extend e b) = Extend (go e) (go <$> b)
    go (Unop op e) = Unop op (go e)
    go (Binop op e w) = Binop op (go e) (go w)

instance (S.Local a, S.Self a) => S.Expr (Expr a) where
  int_ = IntegerLit
  num_ = NumberLit
  str_ = StringLit
  
  unop_ = Unop
  binop_ = Binop
  
instance (S.Local a, S.Self a, S.Extern a) => S.Syntax (Expr a)
  
instance S.Local a => S.Local (Expr a) where
  local_ = Var . S.local_
  
instance S.Self a => S.Self (Expr a) where
  self_ = Var . S.self_
  
instance S.Extern a => S.Extern (Expr a) where
  use_ = Var . S.use_
  
instance S.Field (Expr a) where
  type Compound (Expr a) = Expr a
  
  e #. k = Get (e `At` k)
  
instance S.Path (Expr a)
  
instance S.Tuple (Expr a) where
  type Tup (Expr a) = L Stmt []
  
  tup_ = Group . S.tup_
  
instance S.Block (Expr a) where
  type Rec (Expr a) = L RecStmt []
  
  block_ = Group . S.block_
  
type instance S.Member (Expr a) = Expr a

instance S.Extend (Expr a) where
  type Ext (Expr a) = Group (Expr a)
  
  (#) = Extend
  
  
-- | Name groups are created with (recursive) block or (non-recursive)
--   tuple expressions
data Group a =
    Tup [Stmt a]
  | Block [RecStmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
instance S.Tuple (Group (Expr a)) where
  type Tup (Group (Expr a)) = L Stmt []
  
  tup_ = Tup . getL . S.getS
  
instance S.Block (Group (Expr a)) where
  type Rec (Group (Expr a)) = L RecStmt []
  
  block_ = Block . getL . S.getS
  
type instance S.Member (Group (Expr a)) = Expr a


-- | Statements in a block expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
data RecStmt a =
    Decl (Path Key)
  | Patt `LetRec` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance Applicative f => S.Self1 (L RecStmt f) where
  self1_ = L . pure . Decl . Pure
  
instance Applicative f => S.Field1 (L RecStmt f) where
  type Compound1 (L RecStmt f) = Path Key
  
  p `at1_` k = (L . pure . Decl) (p S.#. k)
  
instance Applicative f => S.RelPath1 (L RecStmt f)

instance Applicative f => S.Let (L RecStmt f) where
  type Lhs (L RecStmt f) = Patt
  
  p #= a = (L . pure) (LetRec p a)
  
instance Applicative f => S.RecStmt (L RecStmt f)

-- | An applicative indexed by a statement type
newtype L s f a = L { getL :: f (s a) }
  deriving (Functor)
  
instance (Functor s, Alt f) => Alt (L s f) where
  L a <!> L b = L (a <!> b)
  
instance (Functor s, Plus f) => Plus (L s f) where
  zero = L zero
  
    
-- | Statements in a tuple expression or decompose pattern can be a
--
--   * Pun statement (define a path to equal the equivalent path in scope/ match
--     a path to an equivalent leaf pattern)
--   * Let statement (define a path to be equal to a value / match a path to
--     a pattern)
--
--   TODO: Possibly allow left hand side of let statements to be full patterns
data Stmt a =
    Pun (Vis (Path Ident) (Path Key))
  | Path Key `Let` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance Applicative f => S.Self1 (L Stmt f) where
  self1_ = L . pure . Pun . Pub . Pure
  
instance Applicative f => S.Local1 (L Stmt f) where
  local1_ = L . pure . Pun . Priv . Pure
  
instance Applicative f => S.Field1 (L Stmt f) where
  type Compound1 (L Stmt f) = Vis (Path Ident) (Path Key)
  
  p `at1_` k = (L . pure . Pun) (p S.#. k)
  
instance Applicative f => S.RelPath1 (L Stmt f)

instance Applicative f => S.LocalPath1 (L Stmt f)
  
instance Applicative f => S.VarPath1 (L Stmt f)

instance Applicative f => S.Let (L Stmt f) where
  type Lhs (L Stmt f) = Path Key
  
  p #= a = (L . pure) (Let p a)

instance Applicative f => S.TupStmt (L Stmt f)
  

-- | A pattern can appear on the lhs of a recursive let statement and can be a
--
--   * Let path pattern (leaf pattern assigns matched value to path)
--   * Decompose pattern (matches a set of paths to corresponding nested patterns)
--   * A decompose pattern with left over pattern (matches set of fields not
--      matched by the decompose pattern)
data Patt =
    LetPath (Vis (Path Ident) (Path Key))
  | Ungroup [Stmt Patt]
  | LetUngroup Patt [Stmt Patt]
  deriving (Eq, Show, Typeable)
  
instance S.Self Patt where
  self_ = LetPath . S.self_
  
instance S.Local Patt where
  local_ = LetPath . S.local_
  
instance S.Field Patt where
  type Compound Patt = Vis (Path Ident) (Path Key)
  
  p #. k = LetPath (p S.#. k)
  
instance S.LocalPath Patt
instance S.RelPath Patt
instance S.VarPath Patt

type instance S.Member Patt = Patt

instance S.Tuple Patt where
  type Tup Patt = L Stmt []
  
  tup_ = Ungroup . getL . S.getS
  
instance S.Extend Patt where
  type Ext Patt = [Stmt Patt]
  
  (#) = LetUngroup
  
type instance S.Member [Stmt Patt] = Patt

instance S.Tuple [Stmt Patt] where
  type Tup [Stmt Patt] = L Stmt []
  
  tup_ = getL . S.getS
  
instance S.Patt Patt


-- | A program guaranteed to be a non-empty set of top level recursive statements
--   with an optional initial global import
data Program a =
  Program (Maybe a) (NonEmpty (RecStmt (Expr (Name Ident Key a))))
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

  
  
