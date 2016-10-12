module Types
  ( Ident(..)
  , Name(..)
  , RelativeRoute(..)
  , Lval(..)
  , ReversibleStmt(..)
  , Rval(..)
  , Stmt(..)
  , Unop(..)
  , Binop(..)
  ) where
import Data.Char
  ( showLitChar )

-- | Print a literal string
showLitString []         s = s
showLitString ('"' : cs) s = "\\\"" ++ (showLitString cs s)
showLitString (c   : cs) s = showLitChar c (showLitString cs s)
  
-- | My-language identifiers
newtype Ident = Ident String
data Name = Ref Ident | Key Rval
data RelativeRoute = RelativeRoute [Name]

instance Show Ident where
  showsPrec _ (Ident s) = showLitString s
instance Show Name where
  show (Ref i) = show i
  show (Key r) = show r
instance Show RelativeRoute where
  show (RelativeRoute xs) = foldr (\a b -> "." ++ show a ++ b) "" xs

-- | My-language lval
data Lval = AbsoluteRoute Ident RelativeRoute | LocalRoute RelativeRoute | ReversibleNode [ReversibleStmt]
data ReversibleStmt = ReversibleAssign RelativeRoute Lval | ReversibleUnpack Lval

instance Show Lval where
  show (AbsoluteRoute s xs) = show s ++ show xs
  show (LocalRoute xs) = show xs
  show (ReversibleNode (x:xs)) = "{ " ++ show x ++ foldr (\a b -> "; " ++ show a ++ b) "" xs ++ " }"
instance Show ReversibleStmt where
  show (ReversibleAssign a b) = show a ++ " = " ++ show b
  show (ReversibleUnpack a) = "*" ++ show a

-- | My language rval
data Rval = Number Double | String String | Lval Lval | Node [Stmt] | App Rval Rval | Unop Unop Rval | Binop Binop Rval Rval
data Stmt = Assign Lval Rval | Eval Rval | Unpack Rval
data Unop = Neg | Not
data Binop = Add | Sub | Prod | Div | Pow | And | Or | Lt | Gt | Eq | Le |Ge

instance Show Rval where
  show (Number n) = show n
  show (String s) = show s
  show (Lval r) = show r
  show (Node (x:xs)) = "{ " ++ show x ++ foldr (\a b -> "; " ++ show a ++ b) "" xs ++ " }"
  show (App a b) = show a ++ "(" ++ show b ++ ")"
  show (Unop s a@(Binop _ _ _)) = show s ++ "(" ++ show a ++ ")"
  show (Unop s a) = show s ++ (show a)
  show (Binop s a@(Binop _ _ _) b@(Binop _ _ _)) = "(" ++ show a ++ ") " ++ show s ++ " (" ++ show b ++ " )"
  show (Binop s a@(Binop _ _ _) b) = "(" ++ show a ++ ") " ++ show s ++ show b
  show (Binop s a b@(Binop _ _ _)) = show a ++ show s ++ " (" ++ show b ++ ")"
  show (Binop s a b) = show a ++ show s ++ show b
instance Show Stmt where
  show (Assign a b) = show a ++ " = " ++ show b
  show (Eval a) = show a
  show (Unpack a) = "*" ++ show a
instance Show Unop where
  showsPrec _ Neg = showLitChar '-'
  showsPrec _ Not = showLitChar '!'
instance Show Binop where
  showsPrec _ Add  = showLitChar '+'
  showsPrec _ Sub  = showLitChar '-'
  showsPrec _ Prod = showLitChar '*'
  showsPrec _ Div  = showLitChar '/'
  showsPrec _ Pow  = showLitChar '^'
  showsPrec _ And  = showLitChar '&'
  showsPrec _ Or   = showLitChar '|'
  showsPrec _ Lt   = showLitChar '<'
  showsPrec _ Gt   = showLitChar '>'
  showsPrec _ Eq   = showLitString "=="
  showsPrec _ Le   = showLitString "<="
  showsPrec _ Ge   = showLitString ">="