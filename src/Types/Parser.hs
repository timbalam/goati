module Types.Parser
  ( Expr(..)
  , BlockExpr(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  , Path(..)
  , SetExpr(..)
  , MatchStmt(..)
  , PathPattern(..)
  , PatternExpr(..)
  , AsStmt(..)
  , ShowMy(..)
  ) where
import Data.Char
  ( showLitChar )
import Data.Foldable
  ( foldl' )
import Data.List.NonEmpty
  ( NonEmpty(..)
  )
import qualified Data.Text as T
  

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
    
    
-- | We will use text to represent my-language identifiers
instance ShowMy T.Text where
  showsMy = showLitString . T.unpack
    
    
-- | High level expression grammar for my-language
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit (StringExpr a)
  | GetEnv a
  | GetSelf a
  | Expr a `Get` a
  | Block (BlockExpr (Stmt a) (Expr a))
  | Expr a `Extend` Expr a
  | Unop Unop (Expr a)
  | Binop Binop (Expr a) (Expr a)
  deriving Eq
  
  
-- | Literal strings are represented as non-empty lists of text
-- | ? We could maybe add some sort of automatic interpolation
type StringExpr a = NonEmpty T.Text

  
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

  
instance ShowMy a => ShowMy (Expr a) where
  showMy (IntegerLit n) =
    show n
    
  showMy (NumberLit n) =
    show n
  
  showMy (StringLit (x:|xs)) =
    show x
      ++ foldMap (\ a -> " " ++ show a) xs
  
  showMy (GetEnv x) =
    showMy x
  
  showMy (GetSelf x) =
    "." ++ showMy x
  
  showMy (y `Get` x) =
    showMy y ++ "." ++ showMy x
  
  showMy (Block expr) =
    showMy expr
            
  showMy (a `Extend` b) =
    showMy a ++ "(" ++ showMy b ++ ")"
  
  showMy (Unop s a@(Binop _ _ _)) =
    showMy s ++ "(" ++ showMy a ++ ")"
  
  showMy (Unop s a) =
    showMy s ++ showMy a
  
  showMy (Binop s a@(Binop _ _ _) b@(Binop _ _ _)) =
    "(" ++ showMy a ++ ") " ++ showMy s ++ " (" ++ showMy b ++ " )"
  
  showMy (Binop s a@(Binop _ _ _) b) =
    "(" ++ showMy a ++ ") " ++ showMy s ++ " " ++ showMy b
  
  showMy (Binop s a b@(Binop _ _ _)) =
    showMy a ++ " " ++ showMy s ++ " (" ++ showMy b ++ ")"
  
  showMy (Binop s a b) =
    showMy a ++ showMy s ++ showMy b


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
data Stmt a =
    Declare (Path a)
  | SetPun (Path a)
  | SetExpr a `Set` Expr a
  deriving Eq

    
instance ShowMy a => ShowMy (Stmt a) where
  showMy (Declare l) =
    showMy  l ++ " ="
    
  showMy (SetPun l) =
    showMy l
  
  showMy (l `Set` r) =
    showMy l ++ " = " ++  showMy r
    
    
    
-- | A path expression for my-language recursively describes a set of nested
-- | fields relative to a self- or environment-defined field
data Path a =
    SelfAt a
  | EnvAt a
  | Path a `At` a
  deriving Eq


-- | A set expression for my-language represents the lhs of a set statement in a
-- | block expression, describing a set of paths to be set using the value computed
-- | on the rhs of the set statement
data SetExpr a =
    SetPath (Path a)
  | SetBlock (BlockExpr (MatchStmt a) (Path a))
  deriving Eq
  
  
-- | Statements allowed in a set block expression (SetBlock constructor for
-- | SetExpr)
-- |  * match a path to be set to the corresponding path of the computed rhs
-- | value of the set statement
-- |  * uses a pattern to extract part of the computed rhs value of the set 
-- | statement and set the extracted value
data MatchStmt a =
    PatternExpr a `Match` SetExpr a
  | MatchPun (Path a)
  deriving Eq
  
  
instance ShowMy a => ShowMy (Path a) where
  showMy (EnvAt x) =
    showMy x
    
  showMy (SelfAt x) =
    "." ++ showMy x
  
  showMy (y `At` x) =
    showMy y ++ "." ++ showMy x
    

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
  

-- | Pattern expr for a path in my-language represents a path relative to some
-- | value being deconstructed.
data PathPattern a =
    SelfAtP a
  | PathPattern a `AtP` a
  deriving Eq
  

-- | Pattern expression represents the transformation of an input value into 
-- | a new value to eventually be set by the rhs of a match statement
data PatternExpr a =
    AsPath (PathPattern a)
  | AsBlock (BlockExpr (AsStmt a) (PathPattern a))
  deriving Eq
  
  
-- | Statements allowed in an block pattern expression (AsBlock constructor for PatternExpr)
-- |  * pun a path from the old value in the new value (i.e. the pattern 
-- | transformation preserves the field)
-- |  * compose patterns (apply lhs then rhs transformations)
data AsStmt a =
    PatternExpr a `As` PatternExpr a
  | AsPun (PathPattern a)
  deriving Eq
  

instance ShowMy a => ShowMy (PathPattern a) where
  showMy (SelfAtP x) =
    "." ++ showMy x
    
  showMy (y `AtP` x) =
    showMy y ++ "." ++ showMy x
    
    
instance ShowMy a => ShowMy (PatternExpr a) where
  showMy (AsPath x) =
    showMy x
    
  showMy (AsBlock expr) =
    showMy expr
      
      
instance ShowMy a => ShowMy (AsStmt a) where
  showMy (l `As` r) =
    showMy l ++ " = " ++ showMy r

  showMy (AsPun l) =
    showMy l
  
  
