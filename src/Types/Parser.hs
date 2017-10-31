{-# LANGUAGE FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveFunctor #-}
module Types.Parser
  ( Expr(..)
  , Path(..)
  , Vis(..)
  , ExprF(..)
  , BlockExpr(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , PathF(..)
  , SetExpr(..)
  , MatchStmt(..)
  , PathPattern
  , PatternExpr
  , AsStmt
  , ShowMy(..)
  ) where
import Data.Char
  ( showLitChar )
import Data.Foldable
  ( foldr )
import Data.List.NonEmpty
  ( NonEmpty(..)
  )
import qualified Data.Text as T
import Control.Monad.Free


data Vis = Priv | Pub


type Expr a = ExprF a (Free (ExprF a) a)


type Path a = PathF (Free PathF a)
  

-- | Extract a valid my-language source text representation from a
-- | Haskell data type representation
class ShowMy a where
  showMy :: a -> String
  showMy x = showsMy x ""
  
  showsMy :: a -> String -> String
  showsMy x s = showMy x ++ s
  
  
-- | Print a literal string
showLitString [] s =
  s

showLitString ('"' : cs) s =
  "\\\"" ++ (showLitString cs s)

showLitString (c   : cs) s =
  showLitChar c (showLitString cs s)
    
   
showLitText :: T.Text -> String -> String
showLitText = showLitString . T.unpack
    
    
-- | High level expression grammar for my-language
-- | Use as: ExprF a (Free (ExprF a) a)
data ExprF a b =
    IntegerLit Integer
  | NumberLit Double
  | StringLit StringExpr
  | GetPath (PathF b)
  | Block (BlockExpr (Stmt a b) (ExprF a b))
  | ExprF a b `Extend` ExprF a b
  | Unop Unop (ExprF a b)
  | Binop Binop (ExprF a b) (ExprF a b)
  deriving Eq
  
instance Functor (ExprF a) where
  fmap _ (IntegerLit i) = IntegerLit i
  
  fmap _ (NumberLit d) = NumberLit d
  
  fmap _ (StringLit s) = StringLit s
  
  fmap f (GetPath p) = GetPath (fmap f p)
  
  fmap f (Block (p :& xs)) = Block (fmap f p :& map (fmap f) xs)
  
  fmap f (Block (Closed xs)) = Block (Closed (map (fmap f) xs))
  
  fmap f (x `Extend` y) = fmap f x `Extend` fmap f y
  
  fmap f (Unop o x) = Unop o (fmap f x)
  
  fmap f (Binop o x y) = Binop o (fmap f x) (fmap f y)
  
  
-- | Literal strings are represented as non-empty lists of text
-- | ? We could maybe add some sort of automatic interpolation
type StringExpr = NonEmpty T.Text

  
data Unop =
    Neg
  | Not
  deriving (Eq, Show)
  
  
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
  deriving (Eq, Show)

  
instance (ShowMy a, ShowMy b) => ShowMy (ExprF a b) where
  showsMy (IntegerLit n) s =
    show n ++ s
    
  showsMy (NumberLit n) s =
    show n ++ s
  
  showsMy (StringLit (x:|xs)) s =
    showLitText x (foldr (\ a x -> " " ++ showLitText a x)  s xs)
  
  showsMy (GetPath path) s =
    showsMy path s
  
  showsMy (Block expr) s =
    showsMy expr s
            
  showsMy (a `Extend` b) s =
    showsMy a ("(" ++ showsMy b (")" ++ s))
  
  showsMy (Unop o a@(Binop _ _ _)) s =
    showsMy o ("(" ++ showsMy a (")" ++ s))
  
  showsMy (Unop o a) s =
    showsMy o (showsMy a s)
  
  showsMy (Binop o a@(Binop _ _ _) b@(Binop _ _ _)) s =
    "(" ++ showsMy a (") " ++ showsMy o (" (" ++ showsMy b (" )" ++ s)))
  
  showsMy (Binop o a@(Binop _ _ _) b) s =
    "(" ++ showsMy a (") " ++ showsMy o (" " ++ showsMy b s))
  
  showsMy (Binop o a b@(Binop _ _ _)) s =
    showsMy a (" " ++ showsMy o (" (" ++ showsMy b (")" ++ s)))
  
  showsMy (Binop o a b) s =
    showsMy a (showsMy o (showsMy b s))


instance ShowMy Unop where
  showsMy Neg =
    showLitChar '-'
  
  showsMy Not =
    showLitChar '!'


instance ShowMy Binop where
  showsMy Add =
    showLitChar '+'
  
  showsMy Sub =
    showLitChar '-'
  
  showsMy Prod =
    showLitChar '*'
  
  showsMy Div =
    showLitChar '/'
  
  showsMy Pow =
    showLitChar '^'
  
  showsMy And =
    showLitChar '&'
  
  showsMy Or =
    showLitChar '|'
  
  showsMy Lt =
    showLitChar '<'
  
  showsMy Gt =
    showLitChar '>'
  
  showsMy Eq =
    showLitString "=="
  
  showsMy Ne =
    showLitString "!="
  
  showsMy Le =
    showLitString "<="
  
  showsMy Ge =
    showLitString ">="
    
        
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data PathF a =
  a `At` T.Text
  deriving (Eq, Functor)
  
  
instance ShowMy a => ShowMy (PathF a) where
  showsMy (a `At` x) s =
    showsMy a ("." ++ showLitText x s)
    

-- | Sequence of statements s with optional trailing statement p
data BlockExpr s p =
    p :& [s]
  | Closed [s]
  deriving Eq
  

instance (ShowMy s, ShowMy p) => ShowMy (BlockExpr s p) where
  showMy (y :& xs) =
    "{ " ++ foldMap (\ a -> showMy a ++ "; ") xs ++ "*" ++ showMy y ++ " }"
    
  showMy (Closed []) =
    "{}"
  
  showMy (Closed (x:xs)) =
    "{ " ++ showMy x ++ foldMap (\ a -> "; " ++ showMy a ++ "; ") xs ++ " }"

  
-- | Statements allowed in a my-language block expression (Block constructor for Expr)
-- |  * declare a path (without a value)
-- |  * define a local path by inheriting an existing path
-- |  * set statement defines a series of paths using a computed value
data Stmt a b =
    Declare (PathF (Free PathF a))
  | SetPun (PathF (Free PathF a))
  | SetExpr a `Set` ExprF a b
  deriving (Eq, Functor)
  
  
instance (ShowMy a, ShowMy (f (Free f a))) => ShowMy (Free f a) where
  showMy (Pure a) =
    showMy a
    
  showMy (Free f) =
    showMy f

    
instance (ShowMy a, ShowMy b) => ShowMy (Stmt a b) where
  showMy (Declare l) =
    showMy  l ++ " ="
    
  showMy (SetPun l) =
    showMy l
  
  showMy (l `Set` r) =
    showMy l ++ " = " ++  showMy r



-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr a =
    SetPath (PathF (Free PathF a))
  | SetBlock (BlockExpr (MatchStmt a) (PathF (Free PathF a)))
  deriving Eq
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt a =
    SetExpr () `Match` SetExpr a
  | MatchPun (PathF (Free PathF a))
  deriving Eq
    

instance ShowMy a => ShowMy (SetExpr a) where
  showMy (SetPath x) =
    showMy x
    
  showMy (SetBlock expr) =
    showMy expr
    
    
instance ShowMy a => ShowMy (MatchStmt a) where
  showMy (r `Match` l) =
    showMy r ++ " = " ++ showMy l
    
  showMy (MatchPun l) =
    showMy l
    
  

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
type PathPattern = PathF (Free PathF ())


type PatternExpr = SetExpr ()

  
instance ShowMy () where
  showsMy () = id
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
type AsStmt = MatchStmt ()
  
  
