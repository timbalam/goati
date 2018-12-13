module Binop
  where
  
infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-
infix 4 #==, #!=, #<, #<=, #>, #>=, :#==, :#!=, :#<, :#<=, :#>, :#>=

data Arith a = 
    Arith a
  | Arith a :#+ Arith a
  | Arith a :#- Arith a
  | Arith a :#* Arith a
  | Arith a :#/ Arith a
  | Arith a :#^ Arith a

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Arith a) where
  (#+) = (:#+)
  (#-) = (:#-)
  (#*) = (:#*)
  (#/) = (:#/)
  (#^) = (:#^)
  
  
-- | Parse an expression observing operator precedence
parseArith :: Arith r => Parser r -> Parser r
parseArith p = parseAdd p where
  parseAdd p = P.chainl1 (parseMul p) addOp where 
    addOp =
      (readAdd >> return (#+))
        <|> (readSub >> return (#-))
        
  parseMul p = P.chainl1 (parsePow p) mulOp where
    mulOp =
      (readMul >> return (#*))
        <|> (readDiv >> return (#/))
        
  parsePow p = P.chainl1 p powOp where
    powOp = readPow >> return (#^)


showArith =
  
  
data Cmp a =
    Cmp a
  | Cmp a :#== Cmp a
  | Cmp a :#!= Cmp a
  | Cmp a :#<  Cmp a
  | Cmp a :#<= Cmp a
  | Cmp a :#>  Cmp a
  | Cmp a :#>= Cmp a
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Cmp a) where
  (#==) = (:#==)
  (#!=) = (:#!=)
  (#>)  = (:#>)
  (#>=) = (:#>=)
  (#<)  = (:#<)
  (#<=) = (:#<=)
  
        
parseCmp :: Cmp_ r => Parser r -> Parser r
parseCmp p =
  do
    a <- p
    (do
       s <- cmpOp
       b <- p
       return (s a b))
      <|> return a
  where
    cmpOp = 
      (readGt >> return (#>))
        <|> (readLt >> return (#<))
        <|> (readEq >> return (#==))
        <|> (readNe >> return (#!=))
        <|> (readGe >> return (#>=))
        <|> (readLe >> return (#<=))
  

 