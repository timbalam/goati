module Types.Intermediate
  ( Assoc
  , Value
  ) where

-- | Print a literal string
showLitString []         s = s
showLitString ('"' : cs) s = "\\\"" ++ (showLitString cs s)
showLitString (c   : cs) s = showLitChar c (showLitString cs s)
    
-- | My-language identifiers
newtype Ident = Ident String
  deriving (Eq, Ord)
data Name a = Ref Ident | Key a
  deriving (Eq, Ord)

instance Show Ident where
  showsPrec _ (Ident s) = showLitString s
instance (Show a) => Show (Name a) where
  show (Ref i) = show i
  show (Key v) = "(" ++ show v ++ ")"
  
type Assoc a = [(Name Value, a)]
data Value a = String String | Number Double | Node Integer (Assoc a) [Value]

instance Eq (Value a) where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Node x _ == Node x' _ = x == x'
  _ == _ = False