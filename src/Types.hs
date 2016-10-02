module Types
  ( Ident(..)
  , Name(..)
  , RelativeRoute(..)
  , Lval(..)
  , ReversibleExpr(..)
  , Rval(..)
  , Expr(..)
  ) where
import Data.Char
  ( showLitChar )

-- | My-language identifiers
newtype Ident = Ident String
data Name = Ref Ident | Key Rval
data RelativeRoute = RelativeRoute [Name]

instance Show Ident where
  showsPrec _ (Ident s) = showLitString s
    where
      showLitString []         s = s
      showLitString ('"' : cs) s = "\\\"" ++ (showLitString cs s)
      showLitString (c   : cs) s = showLitChar c (showLitString cs s)
instance Show Name where
  show (Ref i) = show i
  show (Key r) = show r
instance Show RelativeRoute where
  show (RelativeRoute xs) = foldr (\a b -> "." ++ show a ++ b) "" xs

-- | My-language lval
data Lval = AbsoluteRoute Ident RelativeRoute | LocalRoute RelativeRoute | ReversibleNode [ReversibleExpr]
data ReversibleExpr = ReversibleAssign RelativeRoute Lval | ReversibleUnpack Lval

instance Show Lval where
  show (AbsoluteRoute s xs) = show s ++ show xs
  show (LocalRoute xs) = show xs
  show (ReversibleNode (x:xs)) = "{ " ++ show x ++ foldr (\a b -> "; " ++ show a ++ b) "" xs ++ " }"
instance Show ReversibleExpr where
  show (ReversibleAssign a b) = show a ++ " = " ++ show b
  show (ReversibleUnpack a) = "..." ++ show a

-- | My language rval
data Rval = Number Double | String String | Lval Lval | Node [Expr] | App Rval Rval
data Expr = ReversibleExpr ReversibleExpr | Assign Lval Rval | Eval Rval | Unpack Rval

instance Show Rval where
  show (Number n) = show n
  show (String s) = show s
  show (Lval r) = show r
  show (Node (x:xs)) = "{ " ++ show x ++ foldr (\a b -> "; " ++ show a ++ b) "" xs ++ " }"
  show (App a b) = show a ++ "(" ++ show b ++ ")"
instance Show Expr where
  show (ReversibleExpr a) = show a
  show (Assign a b) = show a ++ " = " ++ show b
  show (Eval a) = show a
  show (Unpack a) = "..." ++ show a
