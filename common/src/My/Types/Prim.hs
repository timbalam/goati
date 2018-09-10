{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
-- | Primitive types for extending core expression
module My.Types.Prim
  ( Prim(..)
  , evalPrim
  )
  where
  
import qualified My.Types.Syntax.Class as S
import My.Types.Syntax.Class
import My.Util (showsUnaryWith, showsBinaryWith, showsTrinaryWith)
import Control.Applicative (liftA2)
import Control.Exception (IOException)
import Control.Monad (ap)
--import Data.Functor.Classes
import Prelude.Extras
import Data.String (IsString(..))
import Data.Text (Text)
 
-- | Primitive types
data Prim a =
    Embed a
  | Number Double
  | Text Text
  | Bool Bool
  | IOError IOException
  | Unop S.Unop (Prim a)
  | Binop S.Binop (Prim a) (Prim a)
  deriving (Functor, Foldable, Traversable)
  
 
evalPrim :: Prim a -> Prim a
evalPrim p = case p of
  Unop op a       -> unop op op (evalPrim a)
  Binop op a b    -> binop op op (evalPrim a) (evalPrim b)
  p               -> p
  where
    unop Not = bool2bool not
    unop Neg = num2num negate
    
    binop Add  = num2num2num (+)
    binop Sub  = num2num2num (-)
    binop Prod = num2num2num (*)
    binop Div  = num2num2num (/)
    binop Pow  = num2num2num (**)
    binop Gt   = num2num2bool (>) 
    binop Lt   = num2num2bool (<)
    binop Eq   = num2num2bool (==)
    binop Ne   = num2num2bool (/=)
    binop Ge   = num2num2bool (>=)
    binop Le   = num2num2bool (<=)
    binop Or   = bool2bool2bool (||)
    binop And  = bool2bool2bool (&&)
    
    bool2bool f op e = maybe (Unop op e) (Bool . f) (bool e)
    num2num f op e = maybe (Unop op e) (Number . f) (num e)
    num2num2num f op a b = maybe (Binop op a b) Number
      (liftA2 f (num a) (num b))
    num2num2bool f op a b = maybe (Binop op a b) Bool
      (liftA2 f (num a) (num b))
    bool2bool2bool f op a b = maybe (Binop op a b) Bool
      (liftA2 f (bool a) (bool b))
    
    bool :: Prim x -> Maybe Bool
    bool a = case a of
      Embed _ -> Nothing
      Bool b -> Just b
      Unop Not _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Lt, Gt, Eq, Ne, Le, Ge, And, Or]
          then Nothing else boole
      _ -> boole
      
    num :: Prim x -> Maybe Double
    num a = case a of
      Embed _ -> Nothing
      Number d -> Just d
      Unop Neg _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Add, Sub, Div, Prod, Pow]
          then Nothing else nume
      _ -> nume
    
    nume = error "eval: number type"
    boole = error "eval: bool type"
    
    
instance Applicative Prim where
  pure = Embed
  (<*>) = ap
  
instance Monad Prim where 
  return = pure
  Embed a      >>= f = f a
  Number d     >>= _ = Number d
  Text t       >>= _ = Text t
  Bool b       >>= _ = Bool b
  IOError e    >>= _ = IOError e
  Unop op a    >>= f = Unop op (a >>= f)
  Binop op a b >>= f = Binop op (a >>= f) (b >>= f)
 
{-
instance Eq a => Eq (Prim a) where
  (==) = eq1
        
instance Eq1 Prim where
  liftEq eq (Embed a)         (Embed b)         = eq a b
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Text sa)         (Text sb)         = sa == sb
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq _  (IOError ea)      (IOError eb)      = ea == eb
  liftEq eq (Unop opa ea)     (Unop opb eb)     = opa == opb && liftEq eq ea eb
  liftEq eq (Binop opa ea wa) (Binop opb eb wb) = opa == opb && liftEq eq ea eb
    && liftEq eq wa wb
  liftEq _  _                 _                 = False
    
instance Show a => Show (Prim a) where
  showsPrec = showsPrec1
  
instance Show1 Prim where
  liftShowsPrec f g i e = case e of
    Embed a      -> showsUnaryWith f "Embed" i a
    Number n     -> showsUnaryWith showsPrec "Number" i n
    Text s       -> showsUnaryWith showsPrec "Text" i s
    Bool b       -> showsUnaryWith showsPrec "Bool" i b
    IOError e    -> showsUnaryWith showsPrec "IOError" i e
    Unop op e    -> showsBinaryWith showsPrec f' "Unop" i op e
    Binop op e w -> showsTrinaryWith showsPrec f' f' "Binop" i op e w
    where
      f' = liftShowsPrec f g
-}

instance Eq a => Eq (Prim a) where
  (==) = (==#)
        
instance Eq1 Prim where
  Embed a         ==# Embed b         = a == b
  Number da       ==# Number db       = da == db
  Text sa         ==# Text sb         = sa == sb
  Bool ba         ==# Bool bb         = ba == bb
  IOError ea      ==# IOError eb      = ea == eb
  Unop opa ea     ==# Unop opb eb     = opa == opb && ea ==# eb
  Binop opa ea wa ==# Binop opb eb wb = opa == opb && ea ==# eb && wa ==# wb
  _               ==# _               = False
    
instance Show a => Show (Prim a) where
  showsPrec = showsPrec1
  
instance Show1 Prim where
  showsPrec1 i e = case e of
    Embed a      -> showsUnaryWith showsPrec "Embed" i a
    Number n     -> showsUnaryWith showsPrec "Number" i n
    Text s       -> showsUnaryWith showsPrec "Text" i s
    Bool b       -> showsUnaryWith showsPrec "Bool" i b
    IOError e    -> showsUnaryWith showsPrec "IOError" i e
    Unop op e    -> showsBinaryWith showsPrec f' "Unop" i op e
    Binop op e w -> showsTrinaryWith showsPrec f' f' "Binop" i op e w
    where
      f' = showsPrec1
    
    
nume = error "error: Num (Prim a)"

instance Num (Prim a) where
  fromInteger = Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Prim a)"

instance Fractional (Prim a) where
  fromRational = Number . fromRational
  (/) = frace
  
instance IsString (Prim a) where
  fromString = Text . fromString

instance S.Lit (Prim a) where
  unop_ op = Unop op
  binop_ op a b = Binop op a b
    