module Types
  ( Ident(..)
  , Name(..)
  , LocalRoute(..)
  , Route(..)
  , Lval(..)
  , Unexpr(..)
  , Rval(..)
  , Expr(..)
  )
where

-- | My-language identifiers
newtype Ident = Ident String
data Name = Ref Ident | Key Rval deriving Show
newtype LocalRoute = LocalRoute [Name]
data Route = Absolute Ident LocalRoute | Local LocalRoute

instance Show Ident where
  show (Ident s) = show s
instance Show LocalRoute where
  show (LocalRoute xs) = foldr (\a b -> show a ++ "." ++ b) "" xs
instance Show Route where
  show (Absolute s xs) = show s ++ "." ++ show xs
  show (Local xs) = show xs

-- | My-language lval
data Lval = Lroute Route | Unnode [Unexpr]
data Unexpr = Unassign LocalRoute Lval | Pack Lval

instance Show Lval where
  show (Lroute r) = show r
  show (Unnode xs) = "{ " ++ foldr (\a b -> show a ++ "; " ++ b) "" xs ++ " }"
instance Show Unexpr where
  show (Unassign a b) = show a ++ " = " ++ show b
  show (Pack a) = "..." ++ show a

-- | My language rval
data Rval = Number Double | String String | Rroute Route | Node [Expr] | App Rval Rval
data Expr = Assign Lval Rval | Eval Rval | Unpack Rval

instance Show Rval where
  show (Number n) = show n
  show (String s) = "\"" ++ show s ++ "\""
  show (Rroute r) = show r
  show (Node xs) = "{ " ++ foldr (\a b -> show a ++ "; " ++ b) "" xs ++ " }"
  show (App a b) = show a ++ "(" ++ show b ++ ")"
instance Show Expr where
  show (Assign a b) = show a ++ " = " ++ show b
  show (Eval a) = show a
  show (Unpack a) = "..." ++ show a
