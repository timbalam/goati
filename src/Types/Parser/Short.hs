{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

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
(.:) :: a -> String -> T.Route a
a .: s = T.Route a (T.Ident s)


dot :: String -> T.Route a
dot = T.Atom . T.Ident


data GenericStmt a b =
    GenericAssign a b
  | GenericDeclare a
  | GenericEval b
  | GenericUnpack
  

(=:) :: a -> b -> GenericStmt a b
(=:) = GenericAssign


var :: a -> GenericStmt a b
var = GenericDeclare


eval :: b -> GenericStmt a b
eval = GenericEval


dots :: GenericStmt a b
dots = GenericUnpack


-- | Rval shorthand
class ToRval a where
  rval :: a -> T.Rval
  
  
instance ToRval T.Rval where
  rval = id
  
  
instance ToRval String where
  rval s = T.Rident (T.Ident s)
  
  
instance ToRval Double where
  rval = T.Number


instance ToRval a => ToRval (T.Route a) where
  rval (T.Route a s) = T.Rroute (T.Route (rval a) s)
  rval (T.Atom s) = T.Rroute (T.Atom s)


quote :: String -> T.Rval
quote = T.String
  
  
node :: (ToLval a, ToRval b) => [GenericStmt a b] -> T.Rval
node xs = T.Rnode (stmt <$> xs)
  where
    stmt :: (ToLval a, ToRval b) => GenericStmt a b -> T.Stmt
    stmt (GenericAssign a b) =
      T.Assign (lval a) (rval b)

    stmt (GenericDeclare a) =
      case lval a of
        T.Laddress l ->
          T.Declare l
        
        _ ->
          error "Error: declare"
      
    stmt (GenericEval b) =
      T.Eval (rval b)


($:) :: (ToRval a, ToRval b) => a -> b -> T.Rval
a $: b = T.App (rval a) (rval b)


not :: ToRval a => a -> T.Rval
not = T.Unop T.Not . rval


neg :: ToRval a => a -> T.Rval
neg = T.Unop T.Neg . rval


_promote op a b = op a b
a &: b = T.Binop T.And (rval a) (rval b)
a |: b = T.Binop T.Or (rval a) (rval b)
(+:) = _promote (T.Binop T.Add)
(-:) = _promote (T.Binop T.Sub)
(*:) = _promote (T.Binop T.Prod)
(/:) = _promote (T.Binop T.Div)
(^:) = _promote (T.Binop T.Pow)
(==:) = _promote (T.Binop T.Eq)
(/=:) = _promote (T.Binop T.Ne)
(>:) = _promote (T.Binop T.Gt)
(<:) = _promote (T.Binop T.Lt)
(>=:) = _promote (T.Binop T.Ge)
(<=:) = _promote (T.Binop T.Le)


-- lval
class ToLaddress a where
  laddr :: a -> T.Laddress

  
instance ToLaddress String where
  laddr = T.Lident . T.Ident
  
  
instance ToLaddress a => ToLaddress (T.Route a) where
  laddr (T.Route a s) = T.Lroute (T.Route (laddr a) s)
  laddr (T.Atom s) = T.Lroute (T.Atom s)
  
  
class ToLval a where
  lval :: a -> T.Lval
  
  
instance ToLaddress a => ToLval a where
  lval = T.Laddress . laddr
  
  
instance ToLval T.Lval where
  lval = id
  
  
lnode :: (ToPlainVal a, ToLval b) => [GenericStmt a b] -> T.Lval
lnode (x:xs) = T.Lnode (go x xs)
  where
    go :: (ToPlainVal a, ToLval b) => GenericStmt a b -> [GenericStmt a b] -> T.LnodeBody
    go GenericUnpack xs =
      T.UnpackFirst (lstmt <$> xs)
    
    go (GenericAssign a b) xs =
      case plainval a of
        T.Packed p ->
          T.LassignPackedFirst p (lval b) (lstmt <$> xs)
        
        T.Unpacked p ->
          T.LassignFirst (T.Lassign p (lval b)) rest
            where
              rest = case xs of 
                [] -> Nothing
                (x:xs) -> Just (go x xs)
    
    go (GenericDeclare _) _ =
      error "Error: declare"
      
    go (GenericEval _) _ =
      error "Error: eval"
    
    
    lstmt :: (ToPlainVal a, ToLval b) => GenericStmt a b -> T.Lstmt
    lstmt (GenericAssign a b) =
      case plainval a of
        T.Packed p ->
          error "Error: unpack"
        
        T.Unpacked p ->
          T.Lassign p (lval b)
  
    lstmt GenericUnpack =
      error "Error: unpack"
  

-- plain val
class ToPlainRoute a where
  plainroute :: a -> T.PlainRoute
  
  
instance ToPlainRoute a => ToPlainRoute (T.Route a) where
  plainroute (T.Route a s) = T.PlainRoute (T.Route (plainroute a) s)
  plainroute (T.Atom s) = T.PlainRoute (T.Atom s)
  
  
class ToPlainRval a where
  plainrval :: a -> T.PlainRval
  
  
instance ToPlainRoute a => ToPlainRval a where
  plainrval = T.PlainRaddress . plainroute


-- plain lval
class ToPlainVal a where
  plainval :: a -> T.PlainLval
  
  
instance ToPlainRval a => ToPlainVal a where
  plainval = T.Unpacked . plainrval
  
  
instance ToPlainVal T.PlainLval where
  plainval = id


pnode :: (ToPlainVal a, ToPlainVal b) => [GenericStmt a b] -> T.PlainLval
pnode (x:xs) = go x xs
  where
    go :: (ToPlainVal a, ToPlainVal b) => GenericStmt a b -> [GenericStmt a b] -> T.PlainLval
    go GenericUnpack xs =
      T.Packed (T.PackedPlainRnode (T.RepackFirst (plainstmt <$> xs)))
    
    go (GenericAssign a b) xs =
      case plainval b of
        T.Packed p -> 
          T.Packed (T.PackedPlainRnode (T.PlainAssignPackedFirst (plainval a) p (plainstmt <$> xs)))
          
        T.Unpacked p ->
          let
            stmt =
              T.PlainAssign (plainval a) p 
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
    
    
    plainstmt :: (ToPlainVal a, ToPlainVal b) => GenericStmt a b -> T.PlainStmt
    plainstmt (GenericAssign a b) =
      case plainval b of
        T.Unpacked p ->
          T.PlainAssign (plainval a) p
          
        T.Packed _ ->
          error "Error: unpack"
          
    plainstmt GenericUnpack =
      error "Error: unpack"

    plainstmt (GenericDeclare _) =
      error "Error: declare"
      
    plainsmt (GenericEval _) =
      error "Error: eval"
  
