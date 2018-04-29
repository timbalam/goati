{-# LANGUAGE FlexibleInstances, FlexibleContexts, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}

-- | Types of my language syntax
module My.Types.Syntax
  ( Unop(..), Binop(..), prec
  , Ident(..), Key(..), StringExpr, Import(..)
  ) where
import qualified Data.Text as T
import Data.Typeable
import Data.String (IsString(..))
--import My.Util
  

-- | Identifier
newtype Ident = I_ T.Text
  deriving (Eq, Ord, Show, Typeable)
  
instance IsString Ident where
  fromString = I_ . fromString

-- | Component name
newtype Key = K_ Ident
  deriving (Eq, Ord, Show, Typeable)

instance IsString Key where
  fromString = K_ . fromString
  
-- | External name
newtype Import = Use Ident
  deriving (Eq, Ord, Show, Typeable)
  
-- | Literal strings are represented as text
--
--   TODO - maybe add some sort of automatic interpolation
type StringExpr = T.Text

  
-- | Unary operators
data Unop =
    Neg
  | Not
  deriving (Eq, Ord, Show, Typeable)
  
  
-- | Binary operators
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
  deriving (Eq, Ord, Show, Typeable)
  
  

-- | a `prec` b is True if a has higher precedence than b
--
-- TODO: Implement relative precedence??
prec :: Binop -> Binop -> Bool
prec _    Pow   = False
prec Pow  _     = True
prec _    Prod  = False
prec _    Div   = False
prec Prod _     = True
prec Div  _     = True
prec _    Add   = False
prec _    Sub   = False
prec Add  _     = True
prec Sub  _     = True
prec _    Eq    = False
prec _    Ne    = False
prec _    Lt    = False
prec _    Gt    = False
prec _    Le    = False
prec _    Ge    = False
prec Eq   _     = True
prec Ne   _     = True
prec Lt   _     = True
prec Gt   _     = True
prec Le   _     = True
prec Ge   _     = True
prec _    And   = False
prec And  _     = True
prec _    Or    = False
--prec Or   _     = True
  
  
