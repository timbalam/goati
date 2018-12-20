{-# LANGUAGE DeriveFunctor, FlexibleInstances #-}
module Goat.Syntax.Unop
  where
  
import Goat.Syntax.Symbol
import Control.Monad.Free
import Text.Parsec.Text (Parser)
  
  
data Neg r = Neg r
  deriving (Eq, Show)
  
class Neg_ r where
  neg_ :: r -> r
  
instance Neg_ (Free Neg r) where
  neg_ m = Free (Neg m)
  
  
  
parseNeg :: Neg_ r => Parser (r -> r)
parseNeg = parseSymbol Sub >> return neg_
  
  
showNeg :: Neg ShowS -> ShowS
showNeg (Neg s) = showSymbol Sub . s