module Types.Parser
  ( FieldId(..)
  , Lval(..)
  , Pattern(..)
  , Selection(..)
  , Lstmt(..)
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
showLitString [] s =
  s

showLitString ('"' : cs) s =
  "\\\"" ++ (showLitString cs s)

showLitString (c   : cs) s =
  showLitChar c (showLitString cs s)
   
   
-- | My-language field identifiers
newtype FieldId = Field String
  deriving (Eq, Ord)

  
instance Show FieldId where
  showsPrec _ (Field s) =
    showLitString s
  
  
-- | My-language lval
data Lval =
    InEnv FieldId
  | InSelf FieldId
  | Lval `In` FieldId
  deriving Eq


data Pattern =
    Address Lval
  | Destructure [Lstmt]
  deriving Eq
  
  
data Selection =
    SelectSelf FieldId
  | Selection `Select` FieldId
  deriving Eq
  
  
data Lstmt =
    Selection `As` Pattern
  | RemainingAs Lval
  deriving Eq

  
instance Show Lval where
  show (InEnv x) =
    show x
    
  show (InSelf x) =
    "." ++ show x
  
  show (x `In` y) =
    show x ++ "." ++ show y


instance Show Pattern where
  show (Address x) =
    show x
    
  show (Destructure (x:xs)) =
       "{ "
    ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs 
    ++ " }"
    
    
instance Show Selection where
  show (SelectSelf x) =
    "." ++ show x
    
  show (x `Select` y) =
    show x ++ "." ++ show y

    
instance Show Lstmt where
  show (r `As` l) =
    show r ++ " = " ++ show l
    
    
  show (RemainingAs l) =
    "*" ++ show l
    
  
-- | My language rval
data Rval =
    NumberLit Double
  | StringLit String
  | GetEnv FieldId
  | GetSelf FieldId
  | Rval `Get` FieldId
  | Structure [Stmt] 
  | Rval `Apply` Rval
  | Unop Unop Rval
  | Binop Binop Rval Rval
  | Import Rval
  deriving Eq

  
data Stmt =
   Declare Lval
 | Pattern `Set` Rval
 | Run Rval
 | Unpack Rval
  deriving Eq

  
data Unop = Neg | Not
  deriving Eq
  
  
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
  deriving Eq

  
instance Show Rval where
  show (NumberLit n) =
    show n
  
  show (StringLit s) =
    show s
  
  show (GetEnv x) =
    show x
    
  show (GetSelf x) =
    "." ++ show x
  
  show (x `Get` y) =
    show x ++ "." ++ show y
  
  show (Structure []) =
    "{}"
  
  show (Structure (x:xs)) =
       "{ "
    ++ foldl' (\b a -> b ++ "; " ++ show a) (show x) xs
    ++ " }"

  show (a `Apply` b) =
    show a ++ "(" ++ show b ++ ")"
  
  show (Unop s a@(Binop _ _ _)) =
    show s ++ "(" ++ show a ++ ")"
  
  show (Unop s a) =
    show s ++ show a
  
  show (Binop s a@(Binop _ _ _) b@(Binop _  _ _)) =
    "(" ++ show a ++ ") " ++ show s ++ " (" ++ show b ++ " )"
  
  show (Binop s a@(Binop _  _ _) b) =
    "(" ++ show a ++ ") " ++ show s ++ " " ++ show b
  
  show (Binop s a b@(Binop _ _ _)) =
    show a ++ " " ++ show s ++ " (" ++ show b ++ ")"
  
  show (Binop s a b) =
    show a ++ show s ++ show b
  
  show (Import s) =
    "from " ++ show s

    
instance Show Stmt where
  show (Declare l) =
    show  l ++ " ="
  
  show (l `Set` r) =
    show l ++ " = " ++  show r
  
  show (Run r) =
    show r
  
  show (Unpack r) =
    "*" ++ show r


instance Show Unop where
  showsPrec _ Neg =
    showLitChar '-'
  
  showsPrec _ Not =
    showLitChar '!'


instance Show Binop where
  showsPrec _ Add =
    showLitChar '+'
  
  showsPrec _ Sub =
    showLitChar '-'
  
  showsPrec _ Prod =
    showLitChar '*'
  
  showsPrec _ Div =
    showLitChar '/'
  
  showsPrec _ Pow =
    showLitChar '^'
  
  showsPrec _ And =
    showLitChar '&'
  
  showsPrec _ Or =
    showLitChar '|'
  
  showsPrec _ Lt =
    showLitChar '<'
  
  showsPrec _ Gt =
    showLitChar '>'
  
  showsPrec _ Eq =
    showLitString "=="
  
  showsPrec _ Ne =
    showLitString "!="
  
  showsPrec _ Le =
    showLitString "<="
  
  showsPrec _ Ge =
    showLitString ">="
