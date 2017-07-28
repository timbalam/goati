{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, FunctionalDependencies #-}

module Types.Parser.Short
where
import Types.Parser

import Data.List.NonEmpty( NonEmpty(..), toList )
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
a .: x = a `Has` Field x


dot :: String -> GenericPath Void
dot x = ContextHas (Field x)


data GenericStmt a b =
    GenericSet a b
  | GenericDeclare a
  | GenericRun b
  | GenericUnpack
  
  
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


dots :: GenericStmt l r
dots =
  GenericUnpack


-- | Rval shorthand
instance Rhs Rval String where
  toRhs = GetEnv . Field
  
  
instance Rhs Rval a => Rhs Rval (GenericPath a) where
  toRhs (ContextHas x) =
    GetSelf x
    
  toRhs (a `Has` x) =
    toRhs a `Get` x
    
    
instance Rhs Rval Void where
  toRhs = absurd
  
          
instance Rhs Rval Rval where
  toRhs = id
  
  
struct :: [GenericStmt Pattern Rval] -> Rval
struct xs = Structure (stmt <$> xs)
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
      
    stmt GenericUnpack =
      error "Error: unpack"

  
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
  
  
destr :: [GenericStmt SelectionPattern Pattern] -> Pattern
destr (x:xs) = Destructure (go x xs)
  where
    go ::
      GenericStmt SelectionPattern Pattern -> [GenericStmt SelectionPattern Pattern] -> Destructure
    go GenericUnpack xs =
      UnpackRemaining (lstmt0 <$> xs)
    
    go (GenericSet (Packed p) l) xs =
      (p `AsP` l) :!! (lstmt0 <$> xs)
      
    go (GenericSet (Unpacked p) l) [] =
      Only (p `As` l)
        
    go (GenericSet (Unpacked p) l) (x:xs) =
       (p `As` l) :|| go x xs
    
    go (GenericDeclare _) _ =
      error "Error: declare"
      
    go (GenericRun _) _ =
      error "Error: eval"
    
    
    lstmt0 :: GenericStmt SelectionPattern Pattern -> Lstmt0
    lstmt0 (GenericSet (Packed p) l) =
      error "Error: unpack"
        
    lstmt0 (GenericSet (Unpacked p) l) =
      p `As` l
  
    lstmt0 GenericUnpack =
      error "Error: unpack"
  

-- selection
class AddressS a where
  toAddrS :: a -> Selection

instance AddressS a => AddressS (GenericPath a) where
  toAddrS (ContextHas x) =
    SelectSelf x
    
  toAddrS (a `Has` x) =
    toAddrS a `Select` x
    
    
instance AddressS Void where
  toAddrS = absurd

  
instance AddressS a => Rhs SelectionPattern (GenericPath a) where
  toRhs = Unpacked . AddressS . toAddrS
  
  
instance Rhs SelectionPattern SelectionPattern where
  toRhs = id
  
  
instance Rhs SelectionPattern a => Lhs SelectionPattern a where
  toLhs = toRhs


descr :: [GenericStmt SelectionPattern SelectionPattern] -> SelectionPattern
descr (x:xs) = go x xs
  where
    go ::
      GenericStmt SelectionPattern SelectionPattern -> [GenericStmt SelectionPattern SelectionPattern] -> SelectionPattern
    go GenericUnpack xs =
      Packed (DescriptionP (PackRemaining (match0 <$> xs)))
    
    go (GenericSet l (Packed p)) xs =
      Packed (DescriptionP ((l `MatchP` p) :!: (match0 <$> xs)))
          
    go (GenericSet l (Unpacked p)) [] =
      Unpacked (Description ((l `Match` p) :| []))
      
    go (GenericSet l (Unpacked p)) (x:xs) =
      case go x xs of
        Packed (DescriptionP body) ->
          Packed (DescriptionP ((l `Match` p) :|: body))
          
        Unpacked (Description body) ->
          Unpacked (Description ((l `Match` p) :| toList body))
    
    go (GenericDeclare _) _ =
      error "Error: declare"
      
    go (GenericRun _) _ =
      error "Error: eval"
    
    
    match0 ::
      GenericStmt SelectionPattern SelectionPattern -> Match0
    match0 (GenericSet l (Unpacked p)) =
      l `Match` p
          
    match0 (GenericSet l (Packed _)) =
      error "Error: unpack"

    match0 (GenericDeclare _) =
      error "Error: declare"
      
    match0 (GenericRun _) =
      error "Error: eval"
          
    match0 GenericUnpack =
      error "Error: unpack"

 
lsref' = dot
lsref = dot
rsref = dot
plainsref = dot

lref' = lref
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
