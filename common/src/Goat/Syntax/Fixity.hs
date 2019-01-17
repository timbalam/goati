{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Trans.Free
  
data Op f a b =
    Term a
  | Op (f b)
  deriving (Eq, Show, Functor)
  
instance Functor f => Bifunctor (Op f) where
  bimap f g (Term a) = Term (f a)
  bimap f g (Op fb) = Op (fmap g fb)
  
hoistOp :: (forall x . f x -> g x) -> Op f a b -> Op g a b
hoistOp f (Term a) = Term a
hoistOp f (Op fb)  = Op (f fb)

showOp
  :: (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (a -> ShowS)
  -> (b -> ShowS)
  -> Op f a b -> ShowS
showOp sf sa sb (Term a) = sa a
showOp sf sa sb (Op fb) = sf sb fb

-- | A series of associated operations.
-- 'p' is a binary operation that is associative in its second type argument.
--
-- e.g. InfixA (b `p` Term a)
-- InfixA (b `p` (Op (InfixA (b `p` Term a))))
-- InfixA (b `p` (Op (InfixA (b `p` (Op (InfixA (b `p` Term a)))))))
newtype InfixA p a b =
  InfixA { runInfixA :: p b (Op (InfixA p a) a b) }

instance Eq (p b (Op (InfixA p a) a b)) => Eq (InfixA p a b)
  where
    InfixA pa  == InfixA pb = pa == pb
 
instance Show (p b (Op (InfixA p a) a b)) => Show (InfixA p a b)
  where
    showsPrec i (InfixA p) = showParen (i>10)
      (showString "InfixA " . showsPrec 11 p)
   
instance Bifunctor p => Functor (InfixA p a) where
  fmap f (InfixA p) = InfixA (bimap f (fmap f) p)
  
instance Bifunctor p => Bifunctor (InfixA p) where
  bimap f g (InfixA p) =
    InfixA (bimap g (hoistOp (first f) . bimap f g) p)

showInfixA
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> InfixA p a b -> ShowS
showInfixA sp sa sb (InfixA p) =
  sp sb (showOp (showInfixA sp sa) sa sb) p
  
  
-- | 
newtype ExpA p a = ExpA (Op (InfixA p a) a (ExpA p a))

instance (Eq (p (ExpA p a) (Op (InfixA p a) a (ExpA p a))), Eq a)
 => Eq (ExpA p a)
  where
    ExpA a == ExpA b = a == b
    
instance
  ( Show (p (ExpA p a) (Op (InfixA p a) a (ExpA p a)))
  , Show a
  ) => Show (ExpA p a)
  where
    showsPrec d (ExpA a) = showParen (d>10)
      (showString "ExpA " . showsPrec 11 a)
      
instance Bifunctor p => Functor (ExpA p) where
  fmap f (ExpA a) = ExpA (hoistOp (first f) (bimap f (fmap f) a))  


showExpA
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> ExpA p a -> ShowS
showExpA sp sa (ExpA o) =
  showOp
    (showInfixA sp sa)
    sa
    (showParen True . showExpA sp sa)
    o
  
-- | A series of interleaved 'f' and 'g'
newtype Inter f g a =
  Inter { runInter :: f (Op (Inter g f) a a) }

instance Eq (f (Op (Inter g f) a a)) => Eq (Inter f g a)
  where
    Inter a == Inter b = a == b
    
instance Show (f (Op (Inter g f) a a)) => Show (Inter f g a)
  where
    showsPrec d (Inter a) = showParen (d>10)
      (showString "Inter " . showsPrec 11 a)

instance (Functor f, Functor g) => Functor (Inter f g) where
  fmap f (Inter a) = Inter (fmap (bimap f f) a)
  
showInter
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Inter f g a -> ShowS
showInter sf sg sa (Inter f) =
  sf (showOp (showInter sg sfp) sa sa) f where
    sfp sx f = showParen True (sf sx f)


newtype Exp f g a =
  Exp { runExp :: Op f (Inter g f a) (Inter g f a) }

instance (Eq (f (Inter g f a)), Eq (g (Op (Inter f g) a a)))
 => Eq (Exp f g a) where
  Exp a == Exp b = a == b
  
instance (Show (f (Inter g f a)), Show (g (Op (Inter f g) a a)))
 => Show (Exp f g a) where
  showsPrec d (Exp a) = showParen (d>10)
    (showString "Exp " . showsPrec 11 a)
    
instance (Functor f, Functor g) => Functor (Exp f g) where
  fmap f (Exp o) = Exp (bimap (fmap f) (fmap f) o)
    
showExp
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Exp f g a -> ShowS
showExp sf sg sa (Exp o) =
  showOp sf (showInter sg sfp sa) (showInter sg sfp sa) o
  where
    sfp sx f = showParen True (sf sx f)
    
    
infixExp
 :: (forall x y . x -> y -> p y x)
 -> Exp (ExpA p) g a
 -> Exp (ExpA p) g a
 -> Exp (ExpA p) g a
infixExp op (Exp a) (Exp b) =
  Exp (Op (ExpA (Op (InfixA (op (f a) (g b))))))
  where
    f :: Op (ExpA p) (Inter g (ExpA p) a) (Inter g (ExpA p) a)
      -> Op (InfixA p (Inter g (ExpA p) a))
            (Inter g (ExpA p) a)
            (ExpA p (Inter g (ExpA p) a))
    f (Term a) = Term a
    f (Op (ExpA o)) = o
            
    g :: Op (ExpA p) (Inter g (ExpA p) a) (Inter g (ExpA p) a)
      -> ExpA p (Inter g (ExpA p) a)
    g (Term a) = ExpA (Term a)
    g (Op e) = e
    -- InfixA
    --  :: p (ExpA p (Inter g (ExpA p) a))
    --       (Op (InfixA p (Inter g (ExpA p) a))
    --           (Inter g (ExpA p) a)
    --           (ExpA p (Inter g (ExpA p) a)))
    --  -> InfixA p
    --            (Inter g (ExpA p) a)
    --            (ExpA p (Inter g (ExpA p) a))
    -- Op
    --  :: InfixA p 
    --            (Inter g (ExpA p) a)
    --            (ExpA p (Inter g (ExpA p) a))
    --  -> Op (InfixA p (Inter g (ExpA p) a))
    --        x
    --        (ExpA p (Inter g (ExpA p) a))
    -- ExpA
    --  :: Op (InfixA p (Inter g (ExpA p) a))
    --        (Inter g (ExpA p) a)
    --        (ExpA p (Inter g (ExpA p) a))
    --  -> ExpA p (Inter g (ExpA p) a)
    -- Op
    --  :: ExpA p (Inter g (ExpA p) a)
    --  -> Op (ExpA p) x (Inter g (ExpA p) a)
    -- Exp
    --  :: Op (ExpA p) (Inter g (ExpA p) a) (Inter g (ExpA p) a) --  -> Exp (ExpA p) g a


--type Bin p a = Either a (p a a)
newtype Infix p a = Infix (p a a)

instance Bifunctor p => Functor (Infix p) where
  fmap f (Infix p) = Infix (bimap f f p)
  
showInfix
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> Infix p a -> ShowS
showInfix sp sa (Infix p) = sp sa sa p
