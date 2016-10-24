module Types
  ( Ident(..)
  , Name(..)
  , Route(..)
  , Address(..)
  , showLitString
  ) where
import Data.Char
  ( showLitChar
  )

-- | Print a literal string
showLitString []         s = s
showLitString ('"' : cs) s = "\\\"" ++ (showLitString cs s)
showLitString (c   : cs) s = showLitChar c (showLitString cs s)
  
-- | My-language identifiers
newtype Ident = Ident String
  deriving (Eq, Ord)
data Name a = Ref Ident | Key a
  deriving (Eq, Ord)
data Route a = One (Name a) | Many (Name a) (Route (Name a))
  deriving (Eq, Ord)
data Address a = Atom Ident | AbsoluteRoute Ident (Route a) | LocalRoute (Route a)
  deriving (Eq, Ord)

instance Show Ident where
  showsPrec _ (Ident s) = showLitString s
instance (Show a) => Show (Name a) where
  show (Ref i) = show i
  show (Key v) = "(" ++ show v ++ ")"
instance (Show a) => Show (Route a) where
  show (Name x) = "." ++ show x
  show (Route x r) = "." ++ show x ++ show r
instance (Show a) => Show (Address a) where
  show (Atom x) = show x
  show (AbsoluteRoute x y) = show x ++ show y
  show (LocalRoute y) = show y

newtype Assoc = Assoc [(Address Value), Value)]
data Value = String String | Number Double | Node Integer Assoc [Value]

instance Eq Value where
  String x == String x' = x == x'
  Number x == Number x' = x == x'
  Node x _ == Node x' _ = x == x'
  _ == _ = False