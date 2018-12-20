{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, RankNTypes, DeriveFunctor #-}

module Goat.Syntax.Binop
  where
  
import Goat.Syntax.Symbol
import qualified Text.Parsec as Parsec
import Text.Parsec ((<|>))
import Text.Parsec.Text (Parser)
import Control.Monad.Free
  
infixr 8 #^, :#^
infixl 7 #*, #/, :#*, :#/
infixl 6 #+, #-, :#+, :#-
infix 4 #==, #!=, #<, #<=, #>, #>=, :#==, :#!=, :#<, :#<=, :#>, :#>=

data ArithOp a b =
    a :#+ b
  | a :#- b
  | a :#* b
  | a :#/ b
  | a :#^ b
  deriving (Eq, Ord, Show) 
  
showArithOp :: (a -> ShowS) -> (b -> ShowS) -> ArithOp a b -> ShowS
showArithOp f g (a :#+ b) = showInfix f g Add a b
showArithOp f g (a :#- b) = showInfix f g Sub a b
showArithOp f g (a :#* b) = showInfix f g Mul a b
showArithOp f g (a :#/ b) = showInfix f g Div a b
showArithOp f g (a :#^ b) = showInfix f g Pow a b

data Precedence p q a b c =
    DefaultLeft (q (p a b) c)
  | DefaultRight (p a (q b c))
  | NoDefault
  
type Prec p q =
    forall a b c
  . (forall x . x -> p a x)
 -> (forall x . x -> q x c)
 -> b 
 -> Precedence p q a b c

precArithOp :: Prec ArithOp ArithOp
precArithOp f g b = case precl of
  _ :#+ _ :#+ _ -> DefaultLeft precl
  _ :#- _ :#+ _ -> DefaultLeft precl
  _ :#+ _ :#- _ -> DefaultLeft precl
  _ :#- _ :#- _ -> DefaultLeft precl
  _ :#* _ :#+ _ -> DefaultLeft precl
  _ :#* _ :#- _ -> DefaultLeft precl
  _ :#/ _ :#+ _ -> DefaultLeft precl
  _ :#/ _ :#- _ -> DefaultLeft precl
  _ :#* _ :#* _ -> DefaultLeft precl
  _ :#* _ :#/ _ -> DefaultLeft precl
  _ :#/ _ :#* _ -> DefaultLeft precl
  _ :#/ _ :#/ _ -> DefaultLeft precl
  _ :#^ _ :#+ _ -> DefaultLeft precl
  _ :#^ _ :#- _ -> DefaultLeft precl
  _ :#^ _ :#* _ -> DefaultLeft precl
  _ :#^ _ :#/ _ -> DefaultLeft precl
  _             -> case precr of
    _ :#+ _ :#* _ -> DefaultRight precr
    _ :#- _ :#* _ -> DefaultRight precr
    _ :#+ _ :#/ _ -> DefaultRight precr
    _ :#- _ :#/ _ -> DefaultRight precr
    _ :#+ _ :#^ _ -> DefaultRight precr
    _ :#- _ :#^ _ -> DefaultRight precr
    _ :#* _ :#^ _ -> DefaultRight precr
    _ :#/ _ :#^ _ -> DefaultRight precr
    _ :#^ _ :#^ _ -> DefaultRight precr
    _             -> NoDefault
  where
    precl = g (f b)
    precr = f (g b)
    
  
type BiPatt p = 
  forall a b c . p a b -> ((forall x y . x -> y -> p x y) -> a -> b -> c) -> c

pattArithOp :: BiPatt ArithOp
pattArithOp p k = case p of
  a :#+ b -> k (:#+) a b
  a :#- b -> k (:#-) a b
  a :#* b -> k (:#*) a b
  a :#/ b -> k (:#/) a b
  a :#^ b -> k (:#^) a b

showInfix
  :: (a -> ShowS) -> (b -> ShowS) -> Symbol -> a -> b -> ShowS
showInfix showa showb op a b =
  showa a
    . showChar ' '
    . showSymbol op
    . showChar ' '
    . showb b

  
data BiExpr p a =
    BinPure a
  | BinOp (p (BiExpr p a) (BiExpr p a))
  deriving (Eq, Show)
  
  
newtype DBiExpr p a = DBiExpr
  { runDBiExpr
      :: forall x y
       . (a -> x)
      -> (forall z . p (p x x) z -> p x z)
      -> (forall z . p z (p x x) -> p z x)
      -> (x -> y)
      -> (p x x -> y)
      -> y
  }
  
dbiPure :: a -> DBiExpr p a
dbiPure a = DBiExpr (\ kp _ _ xy _ -> xy (kp a))

dbiOp
 :: (forall x y . x -> y -> p x y)
 -> DBiExpr p a
 -> DBiExpr p a
 -> DBiExpr p a
dbiOp op (DBiExpr f) (DBiExpr g) = DBiExpr (\ kp kfl kfr xy py ->
  f kp kfl kfr 


  
showsPrecBiExpr
 :: forall a
  . Prec p p
 -> BiPatt p
 -> (a -> ShowS)
 -> (p ShowS ShowS -> ShowS)
 -> BiExpr p a
 -> ShowS
showsPrecBiExpr _    _    showa _     (BinPure a) = showa a
showsPrecBiExpr prec patt showa showp (BiExpr e) = showe e
  where
    showe :: p (BiExpr p a) (BiExpr p a) -> ShowS
    showe = showp . showr . showl

    showl :: forall c . p (BiExpr p a) c -> p ShowS c
    showl p = patt p (\ op e c -> case e of 
      BinPure a -> op (showa a) c
      BinOp p' -> showsPrecL prec patt showe (op p' c))

    showr :: forall b . p b (BiExpr p a) -> p b ShowS
    showr p = patt p (\ op b e -> case e of
      BinPure a -> op b (showa a)
      BinOp p' -> showsPrecR prec patt showe (op b p'))

  
showsPrecDBiExpr
 :: forall a
  . Prec p p
 -> BiPatt p
 -> (a -> ShowS)
 -> (p ShowS ShowS -> ShowS)
 -> DBiExpr p a
 -> ShowS
showsPrecArith prec patt showa showp (DBiExpr f) = 
  f showa showl showr id showp
  where
    showl :: forall c . p (p ShowS ShowS) c -> p ShowS c
    showl p = showsPrecL prec patt showp p

    showr :: forall b . p b (p ShowS ShowS) -> p b ShowS
    showr = showsPrecR prec patt showp p


showsPrecL
 :: Prec p
 -> BiPatt p
 -> (p a b -> ShowS)
 -> p (p a b) c
 -> p ShowS c
showsPrecL prec patt showp p = patt p (\ op p' c ->
  let
    b = patt p' (\ op' a b -> case prec op op' a b c of
        DefaultLeft _ -> False
        _             -> True)
  in  op (showParen b (showp p')) c)

showsPrecR
 :: Prec p
 -> BiPatt p
 -> (p b c -> ShowS)
 -> p a (p b c)
 -> p a ShowS
showsPrecR showp prec patt p = patt p (\ op a p' ->
  let
    b = patt p' (\ op' b c -> case prec op op' a b c of
      DefaultRight _ -> False
      _              -> True)
  in op a (showParen b (showp p)))
  
  
-- | Parse an expression observing operator precedence
parseBiExpr
 :: Prec p p
 -> Patt p
 -> Parser r
 -> Parser (DBiExpr p r -> DBiExpr p r -> DBiExpr p r)
 -> Parser (DBiExpr p r)
parseBinExpr prec patt p op = do 
  a <- p
  go (dbiPure a)
  where
    go e = 
      (do
        f <- op
        b <- p
        goPrec (f e) (dbiPire b))
        <|> return e
        
        
        
        
        
            
parsePrec prec patt p op f a =


 patt (f a) (\ op a b -> case e of
  BinPure _ -> p
  BinOp p'  -> patt p' (\ op' a b -> case prec op op' a b c of
    DefaultLeft  _ -> p
    DefaultRight pp -> patt pp (\ op a e -> BinOp (op a (BinOp e)))
    NoDefault -> fail "operator precedence"))
        
    
  
parseArith :: Arith_ r => Parser r -> Parser r
parseArith p = parseAdd p where
  parseAdd p = Parsec.chainl1 (parseMul p) addOp where 
    addOp =
      (parseSymbol Add >> return (#+))
        <|> (parseSymbol Sub >> return (#-))
        
  parseMul p = Parsec.chainl1 (parsePow p) mulOp where
    mulOp =
      (parseSymbol Mul >> return (#*))
        <|> (parseSymbol Div >> return (#/))
        
  parsePow p = Parsec.chainl1 p powOp where
    powOp = parseSymbol Pow >> return (#^)


type Arith = BinExpr ArithOp

class Arith_ r where
  (#+) :: r -> r -> r
  (#-) :: r -> r -> r
  (#*) :: r -> r -> r
  (#/) :: r -> r -> r
  (#^) :: r -> r -> r
  
instance Arith_ (Arith a) where
  a #+ b = BinOp (a :#+ b)
  a #- b = BinOp (a :#- b)
  a #* b = BinOp (a :#* b)
  a #/ b = BinOp (a :#/ b)
  a #^ b = BinOp (a :#^ b)
  
  
showArith
 :: forall a . (a -> ShowS) -> Arith a -> ShowS
showArith showa = showsPrecBiExpr precArithOp pattArithOp showa (showArithOp id id)
  
  
-- | Parse an expression observing operator precedence
parseArith :: Arith_ r => Parser r -> Parser r
parseArith p = parseAdd p where
  parseAdd p = Parsec.chainl1 (parseMul p) addOp where 
    addOp =
      (parseSymbol Add >> return (#+))
        <|> (parseSymbol Sub >> return (#-))
        
  parseMul p = Parsec.chainl1 (parsePow p) mulOp where
    mulOp =
      (parseSymbol Mul >> return (#*))
        <|> (parseSymbol Div >> return (#/))
        
  parsePow p = Parsec.chainl1 p powOp where
    powOp = parseSymbol Pow >> return (#^)

    
fromArith :: Arith_ r => Arith r -> r
fromArith (ArithPure r) = r
fromArith (ArithOp e) = case e of
  a :#+ b -> fromArithOp (#+) a b
  a :#- b -> fromArithOp (#-) a b
  a :#* b -> fromArithOp (#*) a b
  a :#/ b -> fromArithOp (#/) a b
  a :#^ b -> fromArithOp (#^) a b
  where
    fromArithOp
     :: Arith_ r => (r -> r -> r) -> Arith r -> Arith r -> r
    fromArithOp op a b = fromArith a `op` fromArith b
    
    
data CmpOp a b =
    a :#== b
  | a :#!= b
  | a :#<  b
  | a :#<= b
  | a :#>  b
  | a :#>= b
  deriving (Eq, Show)
  
showCmpOp :: CmpOp ShowS ShowS -> ShowS
showCmpOp (a :#== b) = showInfix Eq a b
showCmpOp (a :#!= b) = showInfix Ne a b
showCmpOp (a :#<  b) = showInfix Lt a b
showCmpOp (a :#<= b) = showInfix Le a b
showCmpOp (a :#>  b) = showInfix Gt a b
showCmpOp (a :#>= b) = showInfix Ge a b

showParenCmpOp :: (CmpOp ShowS ShowS -> Bool) -> CmpOp ShowS ShowS -> ShowS
showParenCmpOp pred a = showParen (pred a) (showCmpOp a)

data Cmp a =
    CmpPure a
  | CmpOp (CmpOp (Cmp a) (Cmp a))
  deriving (Eq, Show)
  
class Cmp_ r where
  (#==) :: r -> r -> r
  (#!=) :: r -> r -> r
  (#>)  :: r -> r -> r
  (#<)  :: r -> r -> r
  (#>=) :: r -> r -> r
  (#<=) :: r -> r -> r
  
instance Cmp_ (Cmp a) where
  a #== b = CmpOp (a :#== b)
  a #!= b = CmpOp (a :#!= b)
  a #>  b = CmpOp (a :#>  b)
  a #>= b = CmpOp (a :#>= b)
  a #<  b = CmpOp (a :#<  b)
  a #<= b = CmpOp (a :#<= b)


showsPrecCmp
 :: forall a
  . (forall x . CmpOp a x -> CmpOp ShowS x)
 -> (forall x . CmpOp x a -> CmpOp x ShowS)
 -> CmpOp (Cmp a) (Cmp a)
 -> CmpOp ShowS ShowS
showsPrecCmp spl spr = show'
  where
    show' = showr . showl
  
    showl :: forall x . CmpOp (Cmp a) x -> CmpOp ShowS x
    showl = withCmpOp (\ op a b -> showlWith (`op` b) a)
    
    showlWith :: forall y . (forall x . x -> CmpOp x y) -> Cmp a -> CmpOp ShowS y
    showlWith ctr (CmpPure a) = spl (ctr a)
    showlWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showr :: forall x . CmpOp x (Cmp a) -> CmpOp x ShowS
    showr = withCmpOp (\ op a b -> showrWith (a `op`) b)
    
    showrWith :: forall x . (forall y . y -> CmpOp x y) -> Cmp a -> CmpOp x ShowS
    showrWith ctr (CmpPure a) = spr (ctr a)
    showrWith ctr (CmpOp e) = ctr (showsPrecCmpOp (show' e))
    
    showsPrecCmpOp = showParenCmpOp (const True)


withCmpOp :: ((forall x y . x -> y -> CmpOp x y) -> a -> b -> c) -> CmpOp a b -> c
withCmpOp op (a :#== b) = op (:#==) a b
withCmpOp op (a :#!= b) = op (:#!=) a b
withCmpOp op (a :#>  b) = op (:#>) a b
withCmpOp op (a :#>= b) = op (:#>=) a b
withCmpOp op (a :#<  b) = op (:#<) a b
withCmpOp op (a :#<= b) = op (:#<=) a b


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
      (parseSymbol Gt >> return (#>))
        <|> (parseSymbol Lt >> return (#<))
        <|> (parseSymbol Eq >> return (#==))
        <|> (parseSymbol Ne >> return (#!=))
        <|> (parseSymbol Ge >> return (#>=))
        <|> (parseSymbol Le >> return (#<=))

    
fromCmp :: Cmp_ r => Cmp r -> r
fromCmp (CmpPure r) = r
fromCmp (CmpOp e) = case e of 
  a :#== b -> fromCmpOp (#==) a b
  a :#!= b -> fromCmpOp (#!=) a b
  a :#>  b -> fromCmpOp (#>) a b
  a :#>= b -> fromCmpOp (#>=) a b
  a :#<  b -> fromCmpOp (#<) a b
  a :#<= b -> fromCmpOp (#<=) a b
  where
    fromCmpOp :: Cmp_ r => (r -> r -> r) -> Cmp r -> Cmp r -> r
    fromCmpOp op a b = fromCmp a `op` fromCmp b
