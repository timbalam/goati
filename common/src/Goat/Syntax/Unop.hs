{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Goat.Syntax.Unop
  where
  
import Control.Monad.Free
  
  
data Neg r = Neg r
  deriving (Eq, Show, Functor)
  
class Neg_ r where
  neg_ :: r -> r
  
instance Neg_ (Free Neg r) where
  neg_ m = Free (Neg m)
  
  
  
parseNeg :: Neg_ r => Parser (r -> r)
  
  
showNeg :: Puts a -> Puts (Neg a)
showNeg showa pred (Neg a) =
    showUnop o . showa (\ _ -> True) a