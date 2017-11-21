{-# LANGUAGE OverloadedStrings, FlexibleInstances #-}
module Types.Parser.Short
where
import Types.Parser
import Parser( Vis(..) )

import qualified Data.Text as T
import Data.String( IsString(..) )
import Data.List.NonEmpty
infixl 9 :.
infixr 8 .^
infixl 7 .*, ./
infixl 6 .+, .-
infix 4 .==, ./=, .<, .<=, .>=, .>
infixr 3 .&
infixr 2 .|
--infixr 0 .=


-- | Operations
class Expressable a where
  toExpr :: a -> Expr (Vis Tag)
  
  
instance Num (Expr a) where
  fromInteger = IntegerLit
  (+) = Binop Add
  (-) = Binop Sub
  (*) = Binop Prod
  negate = Unop Neg
  abs = error "abs"
  signum = error "signum"
  

instance Fractional (Expr a) where
  fromRational = NumberLit . fromRational
  (/) = Binop Div

  
instance IsString (Expr a) where
  fromString = StringLit . fromString
  

instance Expressable (Vis Tag) where
  toExpr = Var
  
  
instance Expressable (Expr (Vis Tag)) where
  toExpr = id
  
  
instance Expressable a => Expressable (GenericPath a) where
  toExpr (a :. x) = Get (toExpr a `At` x)
  
  
  
data GenericPath a = a :. Tag
  
  
liftOp ::
  (Expressable a, Expressable b) => (Expr (Vis Tag) -> Expr (Vis Tag) -> Expr (Vis Tag)) -> a -> b -> Expr (Vis Tag)
liftOp op a b = toExpr a `op` toExpr b


(.&), (.|), (.+), (.-), (.*), (./), (.^), (.==), (./=), (.<), (.<=), (.>), (.>=) :: 
  (Expressable a, Expressable b) => a -> b -> Expr (Vis Tag)
(.&) = liftOp (Binop And)
(.|) = liftOp (Binop Or)
(.+) = liftOp (Binop Add)
(.-) = liftOp (Binop Sub)
(.*) = liftOp (Binop Prod)
(./) = liftOp (Binop Div)
(.^) = liftOp (Binop Pow)
(.==) = liftOp (Binop Eq)
(./=) = liftOp (Binop Ne)
(.<) = liftOp (Binop Lt)
(.<=) = liftOp (Binop Le)
(.>) = liftOp (Binop Gt)
(.>=) = liftOp (Binop Ge)


not, neg :: Expressable a => a -> Expr (Vis Tag)
not = Unop Not . toExpr
neg = Unop Neg . toExpr
  
  




