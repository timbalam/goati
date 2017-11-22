{-# LANGUAGE OverloadedStrings, FlexibleInstances, FlexibleContexts, TypeOperators #-}
module Types.Parser.Short
  ( self
  , env
  , parse
  , GenericPath( (:.) )
  , IsPath
  , GenericStmt( (:=) )
  , GenericSet( B )
  , (.^), (.*), (./), (.+), (.-)
  , (.==), (./=), (.<), (.<=), (.>), (.>=)
  , (.&), (.|), (.$)
  , b
  )
where
import Types.Parser
import Parser( Vis(..) )

import qualified Data.Text as T
import Data.String( IsString(..) )
import Data.List.NonEmpty( NonEmpty(..) )
import Data.Functor.Identity
import Control.Monad.Free
infixl 9 :., .$
infixr 8 .^
infixl 7 .*, ./
infixl 6 .+, .-
infix 4 .==, ./=, .<, .<=, .>=, .>
infixr 3 .&
infixr 2 .|
infixr 0 :=



-- | Overload field address operation
data GenericPath f a =
    GenericVar (f a)
  | GenericPath f a :. T.Text


class IsPath f where
  fromPath :: GenericPath f a -> f a
  
  
liftP2 :: IsPath f => (f r -> f r -> f r) -> GenericPath f r -> GenericPath f r -> GenericPath f r
liftP2 f a b = GenericVar (fromPath a `f` fromPath b)

  

instance (Num (f a), IsPath f) => Num (GenericPath f a) where
  fromInteger = GenericVar . fromInteger
  (+) = liftP2 (+)
  (-) = liftP2 (-)
  (*) = liftP2 (*)
  negate = GenericVar . negate . fromPath
  abs = GenericVar . abs . fromPath
  signum = GenericVar . signum . fromPath
  
  
instance (Fractional (f a), IsPath f) => Fractional (GenericPath f a) where
  fromRational = GenericVar . fromRational
  (/) = liftP2 (/)
  
  
instance IsString (f a) => IsString (GenericPath f a) where
  fromString = GenericVar . fromString

 
-- | Overload literal numbers and strings
instance Num (Expr a) where
  fromInteger = IntegerLit
  (+) = error "+"
  (-) = error "-"
  (*) = error "*"
  negate = error "negate"
  abs = error "abs"
  signum = error "signum"
  

instance Fractional (Expr a) where
  fromRational = NumberLit . fromRational
  (/) = error "/"

  
instance IsString (Expr a) where
  fromString = StringLit . fromString
  
  
instance IsPath Expr where
  fromPath (GenericVar a) = a
  fromPath (p :. x) = Get (fromPath p `At` x)
  
  
-- | Infix operations over generic datatype
type GenExpr = GenericPath Expr

-- Exported specialised version
parse :: GenExpr (Vis Tag) -> Expr (Vis Tag)
parse = fromPath


(.&), (.|), (.+), (.-), (.*), (./), (.^), (.==), (./=), (.<), (.<=), (.>), (.>=), (.$) ::  GenExpr (Vis Tag) -> GenExpr (Vis Tag) -> GenExpr (Vis Tag)
(.&) = liftP2 (Binop And)
(.|) = liftP2 (Binop Or)
(.+) = liftP2 (Binop Add)
(.-) = liftP2 (Binop Sub)
(.*) = liftP2 (Binop Prod)
(./) = liftP2 (Binop Div)
(.^) = liftP2 (Binop Pow)
(.==) = liftP2 (Binop Eq)
(./=) = liftP2 (Binop Ne)
(.<) = liftP2 (Binop Lt)
(.<=) = liftP2 (Binop Le)
(.>) = liftP2 (Binop Gt)
(.>=) = liftP2 (Binop Ge)
(.$) = liftP2 Update


not, neg :: GenExpr (Vis Tag) -> GenExpr (Vis Tag)
not = GenericVar . Unop Not . fromPath
neg = GenericVar . Unop Neg . fromPath


-- | Overload self and env references
class Pointed f where
  point :: a -> f a
  
  
instance Pointed Expr where
  point = Var
  
  
instance Pointed f => Pointed (GenericPath f) where
  point = GenericVar . point
  

self :: Pointed f => T.Text -> f (Vis Tag)
self x = point (Pub x)

env :: Pointed f => T.Text -> f (Vis Tag)
env x = point (Priv x)
  

-- | Overload assignment operator
data GenericStmt l r f a =
    l := r
  | GenericPun (f a)
  
  
instance Pointed f => Pointed (GenericStmt l r f) where
  point = GenericPun . point
  
  
data GenericSet f a =
    GenericPath (f a)
  | B [GenericStmt (f Tag) (GenericSet f a) f a]
  
  
instance Pointed f => Pointed (GenericSet f) where
  point = GenericPath . point
  

-- | block constructor
instance Pointed (Free f) where
  point = Pure
  
instance IsPath Path where
  fromPath (GenericVar a) = a
  fromPath (a :. x) = Free (fromPath a `At` x)
  
  
type GenPath = GenericPath Path


b :: [GenericStmt (GenericSet GenPath (Vis Tag)) (GenExpr (Vis Tag)) GenPath (Vis Tag)] -> GenExpr (Vis Tag)
b = GenericVar . Block . map stmt where
  stmt :: 
    GenericStmt
      (GenericSet GenPath (Vis Tag))
      (GenExpr (Vis Tag))
      GenPath
      (Vis Tag)
    -> Stmt (Vis Tag)
  stmt (l := r) = setexpr l `Set` fromPath r
  stmt (GenericPun l) = SetPun (fromPath l)
  
  setexpr :: GenericSet GenPath a -> SetExpr (Path a) (Path Tag)
  setexpr (GenericPath p) = SetPath (fromPath p)
  setexpr (B stmts) = SetBlock (map matchstmt stmts)
  
  matchstmt :: GenericStmt (GenPath Tag) (GenericSet GenPath a) GenPath a -> MatchStmt (Path a) (Path Tag)
  matchstmt (r := l) = fromPath r `Match` setexpr l
  matchstmt (GenericPun p) = MatchPun (fromPath p)

  



