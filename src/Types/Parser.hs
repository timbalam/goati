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
   
   
--  instance ShowMy String where
--    showsMy =
--      showLitString
    
    
-- | Print a literal text string
instance ShowMy T.Text where
  showsMy = showLitString . T.unpack
    
    
-- | My language grammar
data Expr a =
    IntegerLit Integer
  | NumberLit Double
  | StringLit (StringExpr a)
  | GetEnv a
  | GetSelf a
  | Expr a `Get` a
  | EmptyBlock
  | Block (BlockExpr (Stmt a) (Expr a))
  | Expr a `Extend` Expr a
  | Unop Unop (Expr a)
  | Binop Binop (Expr a) (Expr a)
  deriving Eq
  
  
type StringExpr a = NonEmpty T.Text


data BlockExpr s p =
    p :&& [s]
  | s :& [s]
  deriving Eq

  
data Stmt a =
    Declare (Path a)
  | SetPun (Path a)
  | SetExpr a `Set` Expr a
  deriving Eq

  
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
  
  showMy (EmptyBlock) =
    "{}"
  
  showMy (Block expr) =
    "{"
      ++ showMy expr
      ++ " }"
            
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
          
          

instance (ShowMy s, ShowMy p) => ShowMy (BlockExpr s p) where
  showMy (y :&& xs) =
    foldMap (\ a -> showMy a ++ "; ") xs ++ "*(" ++ showMy y ++ ")"
    
  showMy (x :& xs) =
    showMy x ++ foldMap (\ a -> "; " ++ showMy a ++ "; ") xs

    
instance ShowMy a => ShowMy (Stmt a) where
  showMy (Declare l) =
    showMy  l ++ " ="
    
  showMy (SetPun l) =
    showMy l
  
  showMy (l `Set` r) =
    showMy l ++ " = " ++  showMy r


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
    
    
    
-- | My-language path and set exprs
data Path a =
    SelfAt a
  | EnvAt a
  | Path a `At` a
  deriving Eq


data SetExpr a =
    SetPath (Path a)
  | SetBlock (BlockExpr (MatchStmt a) (Path a))
  deriving Eq
  
  
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
    "{ "
      ++ showMy expr
      ++ " }"
    
    
instance ShowMy a => ShowMy (MatchStmt a) where
  showMy (r `Match` l) =
    showMy r ++ " = " ++ showMy l
    
  showMy (MatchPun l) =
    showMy l
  

-- | Mylanguage path pattern  
data PathPattern a =
    SelfAtP a
  | PathPattern a `AtP` a
  deriving Eq
  

data PatternExpr a =
    AsPath (PathPattern a)
  | AsBlock (BlockExpr (AsStmt a) (PathPattern a))
  deriving Eq
  
  
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
    "{ "
      ++ showMy expr
      ++ " }"
      
      
instance ShowMy a => ShowMy (AsStmt a) where
  showMy (l `As` r) =
    showMy l ++ " = " ++ showMy r

  showMy (AsPun l) =
    showMy l
  
  
