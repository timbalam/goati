module Goat.Syntax.Lit
  where
  
infixl 9 #
infixr 8 #^
infixl 7 #*, #/
infixl 6 #+, #-
infix 4 #==, #!=, #<, #<=, #>=, #>
infixr 3 #&
infixr 2 #|
infixr 1 #=

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
  
  
-- | Operator precedence
--
-- 'First' indicates first operator has precedence.
-- 'Second' indicates second operator has precedence.
-- 'Equal' indicates equal operator precedence.
-- 'None' indicates that explicit disambiguation is required.
data Prec = First | Second | Equal | None
  deriving (Eq, Show)
  

-- | a `prec` b is True if a has higher precedence than b
--
-- TODO: Implement relative precedence??
prec :: Binop -> Binop -> Prec
prec _    Pow   = Second
prec Pow  _     = First
prec _    Prod  = Second
prec _    Div   = Second
prec Prod _     = First
prec Div  _     = First
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
  
  
  
-- | Extend an expression with literal forms
class (Num r, IsString r, Fractional r) => Lit r where
  -- unary and binary operators
  unop_ :: Unop -> r -> r
  binop_ :: Binop -> r -> r -> r

  
(#&), (#|), (#+), (#-), (#*), (#/), (#^), (#==), (#!=), (#<), (#<=), (#>), (#>=)
  :: Lit a => a -> a -> a
not_, neg_ :: Lit a => a -> a

(#&) = binop_ And
(#|) = binop_ Or
(#+) = binop_ Add
(#-) = binop_ Sub
(#*) = binop_ Prod
(#/) = binop_ Div
(#^) = binop_ Pow
(#==) = binop_ Eq
(#!=) = binop_ Ne
(#<) = binop_ Lt
(#<=) = binop_ Le
(#>) = binop_ Gt
(#>=) = binop_ Ge
  
not_ = unop_ Not
neg_ = unop_ Neg