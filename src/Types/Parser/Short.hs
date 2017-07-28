{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, FunctionalDependencies #-}

module Types.Parser.Short
where
import Types.Parser

import Data.Void( Void, absurd )





infixl 9 .:
infixr 8 ^:
infixl 7 *:, /:
infixl 6 +:, -:
infix 4 ==:, /=:, <:, <=:, >=:, >:
infixr 3 &:
infixr 2 |:
infixr 0 =:, $:


-- | Generic operations
data GenericPath a =
    ContextHas FieldId
  | a `Has` FieldId

(.:) :: a -> String -> GenericPath a
a .: x = a `Has` (Field x)


dot :: String -> GenericPath Void
dot x = ContextHas (Field x)


data GenericStmt a b =
    GenericSet a b
  | GenericDeclare a
  | GenericRun b
  | GenericUnpack b
  
  
class Lhs s a where
  toLhs :: a -> s
  

class Rhs s a where
  toRhs :: a -> s
  

(=:) :: (Lhs l a, Rhs r b) => a -> b -> GenericStmt l r
a =: b =
  GenericSet (toLhs a) (toRhs b)

  
var :: Lhs l a => a -> GenericStmt l r
var =
  GenericDeclare . toLhs


run :: Rhs r a => a -> GenericStmt l r
run =
  GenericRun . toRhs


dots :: Rhs r a => a -> GenericStmt l r
dots =
  GenericUnpack . toRhs


-- | Rval shorthand
instance Rhs Rval String where
  toRhs = GetEnv . Field
  
  
instance Rhs Rval a => Rhs Rval (GenericPath a) where
  toRhs (ContextHas x) =
    GetSelf x
        
  toRhs (a `Has` x) =
    toRhs a `Get` x
  
  
instance Rhs Rval (GenericPath Void) where
  toRhs (ContextHas x) =
    GetSelf x
    
          
instance Rhs Rval Rval where
  toRhs = id
  
  
node :: [GenericStmt Pattern Rval] -> Rval
node xs = Structure (stmt <$> xs)
  where
    stmt :: GenericStmt Pattern Rval -> Stmt
    stmt (GenericSet l r) =
      l `Set` r

    stmt (GenericDeclare (Address l)) =
      Declare l
        
    stmt (GenericDeclare (Destructure _)) =
      error "Error: declare"
      
    stmt (GenericRun r) =
      Run r
      
    stmt (GenericUnpack r) =
      Unpack r


not :: Rhs Rval a => a -> Rval
not = Unop Not . toRhs


neg :: Rhs Rval a => a -> Rval
neg = Unop Neg . toRhs


liftRhs :: (Rhs r a, Rhs r b) => (r -> r -> r) -> a -> b -> r
liftRhs op a b = toRhs a `op` toRhs b


(&:), (|:), (+:), (-:), (*:), (/:), (^:), (==:), (/=:), (>:), (<:), (>=:), (<=:), ($:) ::
  (Rhs Rval a, Rhs Rval b) => a -> b -> Rval
(&:) = liftRhs (Binop And)
(|:) = liftRhs (Binop Or)
(+:) = liftRhs (Binop Add)
(-:) = liftRhs (Binop Sub)
(*:) = liftRhs (Binop Prod)
(/:) = liftRhs (Binop Div)
(^:) = liftRhs (Binop Pow)
(==:) = liftRhs (Binop Eq)
(/=:) = liftRhs (Binop Ne)
(>:) = liftRhs (Binop Gt)
(<:) = liftRhs (Binop Lt)
(>=:) = liftRhs (Binop Ge)
(<=:) = liftRhs (Binop Le)
($:) = liftRhs Apply


-- | Lval shorthand
class Addr a where
  toAddr :: a -> Lval

  
instance Addr String where
  toAddr = InEnv . Field

  
instance Addr a => Addr (GenericPath a) where
  toAddr (ContextHas x) =
    InSelf x
    
  toAddr (a `Has` x) =
    toAddr a `In` x
    
instance Addr Void where
  toAddr = absurd
    
    
instance Lhs Pattern String where
  toLhs = Address . toAddr
  

instance Addr a => Lhs Pattern (GenericPath a) where
  toLhs = Address . toAddr
  
  
instance Lhs Pattern Pattern where
  toLhs = id
  
  
instance Lhs Pattern a => Rhs Pattern a where
  toRhs = toLhs
  
  
destr :: [GenericStmt Selection Pattern] -> Pattern
destr (x:xs) = Destructure (lstmt <$> xs)
  where
    lstmt :: GenericStmt Selection Pattern -> Lstmt
    lstmt (GenericSet s l) =
      s `As` l

    lstmt (GenericDeclare s) =
      error "Error: declare"
      
    lstmt (GenericRun s) =
      error "Error: run"
  
    lstmt (GenericUnpack (Address l)) =
      RemainingAs l
      
    lstmt (GenericUnpack (Destructure _)) =
      error "Error: unpack"
  

-- Selection
instance Rhs Selection a => Rhs Selection (GenericPath a) where
  toRhs (ContextHas x) =
    SelectSelf x
    
  toRhs (a `Has` x) =
    toRhs a `Select` x

    
instance Rhs Selection Void where
  toRhs = absurd
  
  
instance Rhs Selection Selection where
  toRhs = id
  
  
instance Rhs Selection a => Lhs Selection a where
  toLhs = toRhs
  
  
lsref' = dot
lsref = dot
rsref = dot
plainsref = dot

lref' = (.:)
lref = (.:)
rref = (.:)
plainref = (.:)

lident' = id
lident = id
rident = id

_add_, _sub_, _prod_, _and_, _ne_, _eq_, _ge_, _le_, _gt_, _lt_, _div_, _pow_, _or_ ::
  (Rhs Rval a, Rhs Rval b) => a -> b -> Rval
_and_ = (&:)
_or_ = (|:)
_add_ = (+:)
_sub_ = (-:)
_prod_ = (*:)
_ne_ = (/=:)
_eq_ = (==:)
_ge_ = (>=:)
_le_ = (<=:)
_gt_ = (>:)
_lt_ = (<:)
_pow_ = (^:)
_div_ = (/:)
