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
import Data.Semigroup (First(..), Semigroup(..))
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

instance (S.Local a, S.Self a) => S.Expr (Expr a)

instance S.Lit (Expr a) where
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
  type Tup (Expr a) = L Stmt [] (Expr a)
  
  tup_ = Group . S.tup_
  
instance S.Block (Expr a) where
  type Rec (Expr a) = L RecStmt [] (Expr a)
  
  block_ = Group . S.block_
  
type instance S.Member (Expr a) = Expr a

instance S.Extend (Expr a) where
  type Ext (Expr a) = Group (Expr a)
  
  (#) = Extend
  
instance S.Defns (Expr a)
  
  
-- | Name groups are created with (recursive) block or (non-recursive)
--   tuple expressions
data Group a =
    Tup [Stmt a]
  | Block [RecStmt a]
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
  
instance S.Tuple (Group (Expr a)) where
  type Tup (Group (Expr a)) = L Stmt [] (Expr a)
  
  tup_ = Tup . getL
  
instance S.Block (Group (Expr a)) where
  type Rec (Group (Expr a)) = L RecStmt [] (Expr a)
  
  block_ = Block . getL
  
type instance S.Member (Group (Expr a)) = Expr a


-- | Statements in a block expression can be a
--
--   * Declare statement (declare a path without a value)
--   * Recursive let statement (define a pattern to be equal to a value)
data RecStmt a =
    Decl (Path Key)
  | Patt `LetRec` a
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance Applicative f => S.Self (L RecStmt f a) where
  self_ = L . pure . Decl . Pure
  
instance Applicative f => S.Field (L RecStmt f a) where
  type Compound (L RecStmt f a) = Path Key
  
  p #. k = (L . pure . Decl) (p S.#. k)
  
instance Applicative f => S.RelPath (L RecStmt f a)

instance Applicative f => S.Let (L RecStmt f a) where
  type Lhs (L RecStmt f a) = Patt
  type Rhs (L RecStmt f a) = a
  
  p #= a = (L . pure) (LetRec p a)
  
instance Applicative f => S.RecStmt (L RecStmt f a)

-- | An applicative indexed by a statement type
newtype L s f a = L { getL :: f (s a) }
  deriving (Functor, Foldable, Traversable)
  
instance Semigroup (f (s a)) => Semigroup (L s f a) where
  L a <> L b = L (a <> b)
  
instance Monoid (f (s a)) => Monoid (L s f a) where
  mempty = L mempty
  
  L a `mappend` L b = L (a `mappend` b)
  
    
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
  
instance Applicative f => S.Self (L Stmt f a) where
  self_ = L . pure . Pun . Pub . Pure
  
instance Applicative f => S.Local (L Stmt f a) where
  local_ = L . pure . Pun . Priv . Pure
  
instance Applicative f => S.Field (L Stmt f a) where
  type Compound (L Stmt f a) = Vis (Path Ident) (Path Key)
  
  p #. k = (L . pure . Pun) (p S.#. k)
  
instance Applicative f => S.RelPath (L Stmt f a)

instance Applicative f => S.LocalPath (L Stmt f a)
  
instance Applicative f => S.VarPath (L Stmt f a)

instance Applicative f => S.Let (L Stmt f a) where
  type Lhs (L Stmt f a) = Path Key
  type Rhs (L Stmt f a) = a
  
  p #= a = (L . pure) (Let p a)

instance Applicative f => S.TupStmt (L Stmt f a)
  

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
  type Tup Patt = L Stmt [] Patt
  
  tup_ = Ungroup . getL
  
instance S.Extend Patt where
  type Ext Patt = L Stmt [] Patt
  
  e # b = LetUngroup e (getL b)
  
type instance S.Member (L Stmt [] Patt) = Patt

instance S.Tuple (L Stmt [] Patt) where
  type Tup (L Stmt [] Patt) = L Stmt [] Patt
  
  tup_ = id
  
instance S.Patt Patt


-- | A program guaranteed to be a non-empty set of top level recursive statements
--   with an optional initial global import
data Program a = Program (Maybe a) (NonEmpty (RecStmt (Expr (Name Ident Key a))))
  deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)
  
instance Semigroup (Program a) where
  Program m ne1 <> Program _ ne2 = Program m (ne1 <> ne2)
  
instance S.Self (Program a) where
  self_ k = Program Nothing (getL (S.self_ k))
  
instance S.Field (Program a) where
  type Compound (Program a) = Path Key
  p #. k = Program Nothing (getL (p S.#. k))
  
instance S.RelPath (Program a)

instance S.Let (Program a) where
  type Lhs (Program a) = Patt
  type Rhs (Program a) = Expr (Name Ident Key a)
  
  p #= e = Program Nothing (getL (p S.#= e))
  
instance S.RecStmt (Program a)

type instance S.Member (Program a) = Expr (Name Ident Key a)
  
instance S.Extern a => S.Global (Program a) where
  type Body (Program a) = Program a
  
  --prog_ xs = Program Nothing (getL (S.getS xs))
  i #... Program _ b = Program (Just (S.use_ i)) b
  
