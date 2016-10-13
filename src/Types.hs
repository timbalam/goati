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
import Data.Foldable
  ( foldl' )

-- | Print a literal string
showLitString []         s = s
showLitString ('"' : cs) s = "\\\"" ++ (showLitString cs s)
showLitString (c   : cs) s = showLitChar c (showLitString cs s)
  
-- | My-language identifiers
newtype Ident = Ident String
data Name = Ref Ident | Key Rval
data RelativeRoute = Name Name | RelativeRoute Name RelativeRoute

instance Show Ident where
  showsPrec _ (Ident s) = showLitString s
instance Show Name where
  show (Ref i) = show i
  show (Key v) = show "(" ++ show v ++ show ")"
instance Show RelativeRoute where
  show (Name x) = "." ++ show x
  show (RelativeRoute x r) = "." ++ show x ++ show r

-- | My-language lval
data Lval = Lident Ident | LabsoluteRoute Ident RelativeRoute | LlocalRoute RelativeRoute | Lnode [ReversibleStmt]
data ReversibleStmt = ReversibleAssign RelativeRoute Lval | ReversibleUnpack Lval

instance Show Lval where
  show (Lident x) = show x
  show (LabsoluteRoute x r) = show x ++ show r
  show (LlocalRoute r) = show r
  show (Lnode (x:xs)) = "{ " ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs ++ " }"
instance Show ReversibleStmt where
  show (ReversibleAssign r l) = show r ++ " = " ++ show l
  show (ReversibleUnpack l) = "*" ++ show l

-- | My language rval
data Rval = Number Double | String String | Rident Ident | RabsoluteRoute Rval RelativeRoute | RlocalRoute RelativeRoute | Rnode [Stmt] | App Rval Rval | Unop Unop Rval | Binop Binop Rval Rval
data Stmt = Assign Lval Rval | Eval Rval | Unpack Rval
data Unop = Neg | Not
data Binop = Add | Sub | Prod | Div | Pow | And | Or | Lt | Gt | Eq | Le |Ge

instance Show Rval where
  show (Number n) = show n
  show (String s) = show s
  show (Rident i) = show i
  show (RabsoluteRoute r x) = show r ++ show x
  show (RlocalRoute x) = show x
  show (Rnode (x:xs)) = "{ " ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs ++ " }"
  show (App a b) = show a ++ "(" ++ show b ++ ")"
  show (Unop s a@(Binop _ _ _)) = show s ++ "(" ++ show a ++ ")"
  show (Unop s a) = show s ++ (show a)
  show (Binop s a@(Binop _ _ _) b@(Binop _ _ _)) = "(" ++ show a ++ ") " ++ show s ++ " (" ++ show b ++ " )"
  show (Binop s a@(Binop _ _ _) b) = "(" ++ show a ++ ") " ++ show s ++ show b
  show (Binop s a b@(Binop _ _ _)) = show a ++ show s ++ " (" ++ show b ++ ")"
  show (Binop s a b) = show a ++ show s ++ show b
instance Show Stmt where
  show (Assign l r) = show l ++ " = " ++ show r
  show (Eval r) = show r
  show (Unpack r) = "*" ++ show r
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