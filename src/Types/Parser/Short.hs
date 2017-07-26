{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, FunctionalDependencies #-}

module Types.Parser.Short
where
import qualified Types.Parser as T

import Data.List.NonEmpty( NonEmpty(..), toList )





infixl 9 .:
infixr 8 ^:
infixl 7 *:, /:
infixl 6 +:, -:
infix 4 ==:, /=:, <:, <=:, >=:, >:
infixr 3 &:
infixr 2 |:
infixr 0 =:, $:


-- | Generic operations
data AbsoluteRoute a = Abs a [T.Ident]


data RelativeRoute = Rel (NonEmpty T.Ident)


class Route s where
  extend :: s -> String -> s
  
 
instance Route (AbsoluteRoute a) where
  extend (Abs s xs) x =
    Abs s (T.Ident x : xs)
  

instance Route RelativeRoute where
  extend (Rel xs) x =
    Rel (T.Ident x :| toList xs)


class Routable s a | a -> s where
  toRoute :: a -> s
  
  
instance Routable (AbsoluteRoute a) (AbsoluteRoute a) where
  toRoute = id
  
  
instance Routable RelativeRoute RelativeRoute where
  toRoute = id
  
  
(.:) :: (Route s, Routable s a) => a -> String -> s
a .: x = extend (toRoute a) x


dot :: String -> RelativeRoute
dot x =
  Rel (T.Ident x :| [])


data GenericStmt a b =
    GenericAssign a b
  | GenericDeclare a
  | GenericEval b
  | GenericUnpack
  
  
class Lhs s a where
  toLhs :: a -> s
  

class Rhs s a where
  toRhs :: a -> s
  

(=:) :: (Lhs l a, Rhs r b) => a -> b -> GenericStmt l r
a =: b =
  GenericAssign (toLhs a) (toRhs b)

  
var :: Lhs l a => a -> GenericStmt l r
var =
  GenericDeclare . toLhs


eval :: Rhs r a => a -> GenericStmt l r
eval =
  GenericEval . toRhs


dots :: GenericStmt l r
dots =
  GenericUnpack


-- | Rval shorthand
instance Routable (AbsoluteRoute String) String where
  toRoute s = Abs s []
  

instance Routable (AbsoluteRoute T.Rval) T.Rval where
  toRoute r = Abs r []
  
  
instance Rhs T.Rval String where
  toRhs = T.Rident . T.Ident
  
  
instance Rhs T.Rval a => Rhs T.Rval (AbsoluteRoute a) where
  toRhs (Abs a xs) =
    go xs
      where
        go [] =
          toRhs a
        
        go (x:xs) =
          T.Rroute (T.Route (go xs) x)
  
  
instance Rhs T.Rval RelativeRoute where
  toRhs (Rel (x:|xs)) =
    go xs
      where
        go [] =
          T.Rroute (T.Atom x)
          
        go (x1:xs) =
          T.Rroute (T.Route (go xs) x1)
          
instance Rhs T.Rval T.Rval where
  toRhs = id
  
  
node :: [GenericStmt T.Lval T.Rval] -> T.Rval
node xs = T.Rnode (stmt <$> xs)
  where
    stmt :: GenericStmt T.Lval T.Rval -> T.Stmt
    stmt (GenericAssign l r) =
      T.Assign l r

    stmt (GenericDeclare l) =
      case l of
        T.Laddress a ->
          T.Declare a
        
        _ ->
          error "Error: declare"
      
    stmt (GenericEval r) =
      T.Eval r
      

($:) :: (Rhs T.Rval a, Rhs T.Rval b) => a -> b -> T.Rval
a $: b = T.App (toRhs a) (toRhs b)


not :: Rhs T.Rval a => a -> T.Rval
not = T.Unop T.Not . toRhs


neg :: Rhs T.Rval a => a -> T.Rval
neg = T.Unop T.Neg . toRhs


liftRhs :: (Rhs r a, Rhs r b) => (r -> r -> r) -> a -> b -> r
liftRhs op a b = op (toRhs a) (toRhs b)


(&:), (|:), (+:), (-:), (*:), (/:), (^:), (==:), (/=:), (>:), (<:), (>=:), (<=:) ::
  (Rhs T.Rval a, Rhs T.Rval b) => a -> b -> T.Rval
(&:) = liftRhs (T.Binop T.And)
(|:) = liftRhs (T.Binop T.Or)
(+:) = liftRhs (T.Binop T.Add)
(-:) = liftRhs (T.Binop T.Sub)
(*:) = liftRhs (T.Binop T.Prod)
(/:) = liftRhs (T.Binop T.Div)
(^:) = liftRhs (T.Binop T.Pow)
(==:) = liftRhs (T.Binop T.Eq)
(/=:) = liftRhs (T.Binop T.Ne)
(>:) = liftRhs (T.Binop T.Gt)
(<:) = liftRhs (T.Binop T.Lt)
(>=:) = liftRhs (T.Binop T.Ge)
(<=:) = liftRhs (T.Binop T.Le)


-- | Lval shorthand
class Laddressable a where
  toLaddr :: a -> T.Laddress

  
instance Laddressable String where
  toLaddr = T.Lident . T.Ident

  
instance Laddressable a => Laddressable (AbsoluteRoute a) where
  toLaddr (Abs a xs) =
    go xs
      where
        go [] =
          toLaddr a
          
        go (x:xs) =
          T.Lroute (T.Route (go xs) x)
          
    
instance Laddressable RelativeRoute where
  toLaddr (Rel (x:|xs)) =
    go xs
      where
        go [] =
          T.Lroute (T.Atom x)
    
        go (x1:xs) =
          T.Lroute (T.Route (go xs) x1)
    
    
instance Lhs T.Lval String where
  toLhs = T.Laddress . toLaddr
  

instance Laddressable a => Lhs T.Lval (AbsoluteRoute a) where
  toLhs = T.Laddress . toLaddr
  
  
instance Lhs T.Lval RelativeRoute where
  toLhs = T.Laddress . toLaddr
  
  
instance Lhs T.Lval T.Lval where
  toLhs = id
  
  
instance Lhs T.Lval a => Rhs T.Lval a where
  toRhs = toLhs
  
  
lnode :: [GenericStmt T.PlainLval T.Lval] -> T.Lval
lnode (x:xs) = T.Lnode (go x xs)
  where
    go :: GenericStmt T.PlainLval T.Lval -> [GenericStmt T.PlainLval T.Lval] -> T.LnodeBody
    go GenericUnpack xs =
      T.UnpackFirst (lstmt <$> xs)
    
    go (GenericAssign (T.Packed p) l) xs =
      T.LassignPackedFirst p l (lstmt <$> xs)
        
    go (GenericAssign (T.Unpacked p) l) xs =
      T.LassignFirst (T.Lassign p l) rest
        where
          rest = case xs of 
            [] -> Nothing
            (x:xs) -> Just (go x xs)
    
    go (GenericDeclare _) _ =
      error "Error: declare"
      
    go (GenericEval _) _ =
      error "Error: eval"
    
    
    lstmt :: GenericStmt T.PlainLval T.Lval -> T.Lstmt
    lstmt (GenericAssign (T.Packed p) l) =
      error "Error: unpack"
        
    lstmt (GenericAssign (T.Unpacked p) l) =
      T.Lassign p l
  
    lstmt GenericUnpack =
      error "Error: unpack"
  

-- plain val
instance Rhs T.PlainRoute RelativeRoute where
  toRhs (Rel (x:|xs)) =
    go xs
      where
        go [] =
          T.PlainRoute (T.Atom x)
        
        go (x1:xs) =
          T.PlainRoute (T.Route (go xs) x1)
  
  
instance Rhs T.PlainRoute T.PlainRoute where
  toRhs = id

  
instance Rhs T.PlainRoute a => Rhs T.PlainRval a where
  toRhs = T.PlainRaddress . toRhs
  
  
instance Rhs T.PlainRval T.PlainRval where
  toRhs = id
  
  
instance Rhs T.PlainRval a => Rhs T.PlainLval a where
  toRhs = T.Unpacked . toRhs
  
  
instance Rhs T.PlainLval T.PlainLval where
  toRhs = id
  
  
instance Rhs T.PlainLval a => Lhs T.PlainLval a where
  toLhs = toRhs


pnode :: [GenericStmt T.PlainLval T.PlainLval] -> T.PlainLval
pnode (x:xs) = go x xs
  where
    go :: GenericStmt T.PlainLval T.PlainLval -> [GenericStmt T.PlainLval T.PlainLval] -> T.PlainLval
    go GenericUnpack xs =
      T.Packed (T.PackedPlainRnode (T.RepackFirst (plainstmt <$> xs)))
    
    go (GenericAssign l (T.Packed p)) xs =
      T.Packed (T.PackedPlainRnode (T.PlainAssignPackedFirst l p (plainstmt <$> xs)))
          
    go (GenericAssign l (T.Unpacked p)) xs =
      let
        stmt =
          T.PlainAssign l p 
      in 
        case xs of
          [] ->
            (T.Unpacked . T.PlainRnode . T.PlainRnodeBody) (stmt :| [])
              
          (x:xs) ->
            case go x xs of
              T.Packed (T.PackedPlainRnode body) ->
                T.Packed (T.PackedPlainRnode (T.PlainAssignFirst stmt body))
                
              T.Unpacked (T.PlainRnode (T.PlainRnodeBody xs)) ->
                T.Unpacked (T.PlainRnode (T.PlainRnodeBody (stmt :| toList xs)))
    
    go (GenericDeclare _) _ =
      error "Error: declare"
      
    go (GenericEval _) _ =
      error "Error: eval"
    
    
    plainstmt :: GenericStmt T.PlainLval T.PlainLval -> T.PlainStmt
    plainstmt (GenericAssign l (T.Unpacked p)) =
      T.PlainAssign l p
          
    plainstmt (GenericAssign l (T.Packed _)) =
      error "Error: unpack"
          
    plainstmt GenericUnpack =
      error "Error: unpack"

    plainstmt (GenericDeclare _) =
      error "Error: declare"
      
    plainsmt (GenericEval _) =
      error "Error: eval"
  
  
-- | Orphans
instance Num T.Rval where
  T.Number x + T.Number y =
    T.Number (x + y)
  
  
  T.Number x - T.Number y =
     T.Number (x - y)
  
  
  T.Number x * T.Number y =
    T.Number (x * y)
  
  
  abs (T.Number x) =
    T.Number (abs x)
  
  
  signum (T.Number x) =
    T.Number (signum x)
  
  
  fromInteger =
    T.Number . fromInteger
    
    
instance Fractional T.Rval where
  T.Number a / T.Number b = T.Number (a / b)
  
  
  fromRational = T.Number . fromRational

 
lsref' = dot
lsref = dot
rsref = dot
plainsref = dot

lref' :: Routable (AbsoluteRoute a) a => a -> String -> AbsoluteRoute a
lref' = lref

lref, rref :: (Route b, Routable b a) => a -> String -> b
lref = (.:)
rref = (.:)

plainref :: Routable RelativeRoute a => a -> String -> RelativeRoute
plainref = (.:)

lident' = id
lident = id
rident = id

_add_, _sub_, _prod_, _and_, _ne_, _eq_, _ge_, _le_, _gt_, _lt_, _div_, _pow_, _or_ ::
  (Rhs T.Rval a, Rhs T.Rval b) => a -> b -> T.Rval
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
