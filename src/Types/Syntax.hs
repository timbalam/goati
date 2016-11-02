module Types.Syntax
  ( Ident(..)
  , Name(..)
  , Route(..)
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
import Types.Intermediate
  ( Ident(..)
  , Name(..)
  , showLitString
  )

-- | My-language identifiers
data Route a = One (Name a) | Many (Name a) (Route (Name a))

instance (Show a) => Show (Route a) where
  show (Name x) = "." ++ show x
  show (Route x r) = "." ++ show x ++ show r
  
-- | My-language lval
data Lval = Lident Ident | LabsoluteRoute Ident (Route Rval) | LlocalRoute (Route Rval) | Lnode [ReversibleStmt]
data ReversibleStmt = ReversibleAssign Route Lval | ReversibleUnpack Lval

instance Show Lval where
  show (Lident x) = show x
  show (LabsoluteRoute x y) = show x ++ show y
  show (LlocalRoute y) = show y
  show (Lnode (x:xs)) = "{ " ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs ++ " }"
instance Show ReversibleStmt where
  show (ReversibleAssign r l) = show r ++ " = " ++ show l
  show (ReversibleUnpack l) = "*" ++ show l
  
-- | My language rval
data Rval = Number Double | String String | Rident Ident | RabsoluteRoute Rval (Route Rval) | RlocalRoute (Route Rval) | Rnode [Stmt] | App Rval Rval | Unop Unop Rval | Binop Binop Rval Rval
data Stmt = Assign Lval Rval | Eval Rval | Unpack Rval
data Unop = Neg | Not
data Binop = Add | Sub | Prod | Div | Pow | And | Or | Lt | Gt | Eq | Le |Ge

instance Show Rval where
  show (Number n) = show n
  show (String s) = show s
  show (Rident x) = show x
  show (RabsoluteRoute x y) = show x ++ show y
  show (RlocalRoute y) = show y
  show (Rnode []) = "{}"
  show (Rnode (x:xs)) = "{ " ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs ++ " }"
  show (App a b) = show a ++ "(" ++ show b ++ ")"
  show (Unop s a@(Binop _ _ _)) = show s ++ "(" ++ show a ++ ")"
  show (Unop s a) = show s ++ (show a)
  show (Binop s a@(Binop _ _ _) b@(Binop _ _ _)) = "(" ++ show a ++ ") " ++ show s ++ " (" ++ show b ++ " )"
  show (Binop s a@(Binop _ _ _) b) = "(" ++ show a ++ ") " ++ show s ++ " " ++ show b
  show (Binop s a b@(Binop _ _ _)) = show a ++ " " ++ show s ++ " (" ++ show b ++ ")"
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

instance Eq Rval where
  Number x == Number y = x == y
  String x == String y = x == y
  Rnode x _ == Rnode y _ = x == y
  _ == _ = False