{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Trans.Free


newtype Wrap a = Wrap a

newtype Emb f g = Emb (f (g a))
 
newtype Exp a b = Term a | Exp b
  deriving (Eq, Show, Functor)
  
type Exp' f a b = Exp b (f (Exp a (Wrap b)))

-- | A series of associated operations.
-- 'p' is a binary operation that is associative in its second type argument.
newtype OpA p f a =
  OpA (p (Exp (Exp a
                   (Wrap (OpA p f a)))
              (f (Exp a (Wrap (OpA p f a)))))
         (Exp a
              (Exp (OpA p f a)
                   (f (Exp a (Wrap (OpA p f a)))))))
  

newtype InfixA p a b =
  InfixA { runInfixA :: p a (Op (InfixA p a) b) }

instance Eq (p a (Op (InfixA p a) b)) => Eq (InfixA p a b)
  where
    InfixA pa  == InfixA pb = pa == pb
 
instance Show (p a (Op (InfixA p a) b)) => Show (InfixA p a b)
  where
    showsPrec i (InfixA p) = showParen (i>10)
      (showString "InfixA " . showsPrec 11 p)
   
instance Bifunctor p => Functor (InfixA p a) where
  fmap f (InfixA p) = InfixA (second (fmap f) p)
  
instance Bifunctor p => Bifunctor (InfixA p) where
  bimap f g (InfixA p) =
    InfixA (bimap f (hoistOp (first f) . fmap g) p)

showInfixA
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> InfixA p a b -> ShowS
showInfixA sp sa sb (InfixA p) =
  sp sa (showOp (showInfixA sp sa) sb) p
  
  
-- | 
newtype ExpA p a =
  ExpA (Op (InfixA p (ExpA p a)) a)
-- ExpA (Op (InfixA p a) a (ExpA p a))

instance
  ( Eq (p (ExpA p a) (Op (InfixA p (ExpA p a)) a))
  , Eq a)
 => Eq (ExpA p a)
  where
    ExpA a == ExpA b = a == b
    
instance
  ( Show (p (ExpA p a) (Op (InfixA p (ExpA p a)) a))
  , Show a
  ) => Show (ExpA p a)
  where
    showsPrec d (ExpA a) = showParen (d>10)
      (showString "ExpA " . showsPrec 11 a)
      
instance Bifunctor p => Functor (ExpA p) where
  fmap f (ExpA a) = ExpA (hoistOp (first (fmap f)) (fmap f a))  


showExpA
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> ExpA p a -> ShowS
showExpA sp sa (ExpA o) =
  showOp (showInfixA sp sep) sa o
  where
    sep e = showParen True (showExpA sp sa e)
  
-- | A series of interleaved 'f' and 'g'
newtype Inter f g a =
  Inter { runInter :: f (Op (Inter g f) a) }

instance Eq (f (Op (Inter g f) a)) => Eq (Inter f g a)
  where
    Inter a == Inter b = a == b
    
instance Show (f (Op (Inter g f) a)) => Show (Inter f g a)
  where
    showsPrec d (Inter a) = showParen (d>10)
      (showString "Inter " . showsPrec 11 a)

instance (Functor f, Functor g) => Functor (Inter f g) where
  fmap f (Inter a) = Inter (fmap (fmap f) a)
  
showInter
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Inter f g a -> ShowS
showInter sf sg sa (Inter f) =
  sf (showOp (showInter sg sfp) sa) f where
    sfp sx f = showParen True (sf sx f)


data Exp f g a =
    ExpF (Inter f g a)
  | ExpG (Inter g f a)

instance (Eq (f (Op (Inter g f) a)), Eq (g (Op (Inter f g) a)))
 => Eq (Exp f g a) where
  ExpF a == ExpF b = a == b
  ExpG a == ExpG b = a == b
  _      == _      = False
  
instance (Show (f (Op (Inter g f) a)), Show (g (Op (Inter f g) a)))
 => Show (Exp f g a) where
  showsPrec d (ExpF a) = showParen (d>10)
    (showString "ExpF " . showsPrec 11 a)
  showsPrec d (ExpG a) = showParen (d>10)
    (showString "ExpG " . showsPrec 11 a)
    
instance (Functor f, Functor g) => Functor (Exp f g) where
  fmap f (ExpF a) = ExpF (fmap f a)
  fmap f (ExpG a) = ExpG (fmap f a)
    
showExp
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Exp f g a -> ShowS
showExp sf sg sa e = case e of
  ExpF a -> showInter sf sg sa a
  ExpG a -> showInter sg sfp sa a
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
    f :: Op (ExpA p) (Inter g (ExpA p) a)
      -> Op (InfixA p (ExpA p (Inter g (ExpA p) a)))
            (Inter g (ExpA p) a)
    f (Term a) = Term a
    f (Op (ExpA o)) = o
            
    g :: Op (ExpA p) (Inter g (ExpA p) a)
      -> ExpA p (Inter g (ExpA p) a)
    g (Term a) = ExpA (Term a)
    g (Op e) = e
-- InfixA
--  :: p (ExpA p (Inter g (ExpA p) a))
--       (Op (InfixA p (ExpA p (Inter g (ExpA p) a)))
--           (Inter g (ExpA p) a))
--  -> InfixA p
--            (ExpA p (Inter g (ExpA p) a))
--            (Inter g (ExpA p) a)
-- Op
--  :: InfixA p 
--            (ExpA p (Inter g (ExpA p) a))
--            (Inter g (ExpA p) a)
--  -> Op (InfixA p (ExpA p (Inter g (ExpA p) a)))
--        (Inter g (ExpA p) a))
-- ExpA
--  :: Op (InfixA p (ExpA p (Inter g (ExpA p) a)))
--        (Inter g (ExpA p) a)
--  -> ExpA p (Inter g (ExpA p) a)
-- Op
--  :: ExpA p (Inter g (ExpA p) a)
--  -> Op (ExpA p) (Inter g (ExpA p) a)
-- Exp
--  :: Op (ExpA p) (Inter g (ExpA p) a)
--  -> Exp (ExpA p) g a

liftInfixExp
  :: (forall x . g x -> g x -> g x)
  -> Exp f g a
  -> Exp f g a
  -> Exp f g a
liftInfixExp lop (Exp a) (Exp b) =
  Exp (Term (Inter (lop (f a) (f b))))
  where
    f :: Op f (Inter g f a)
      -> g (Op (Inter f g) a)
    f (Term (Inter g)) = g
    f (Op (
-- Inter
--   :: g (Op (Inter f g) a)
--   -> Inter g f a
-- Term
--  :: Inter g f a -> Op f (Inter g f a)
-- Exp
--  :: Op f (Inter g f a)
--  -> Exp f g a


--type Bin p a = Either a (p a a)
newtype Infix p a = Infix (p a a)

instance Bifunctor p => Functor (Infix p) where
  fmap f (Infix p) = Infix (bimap f f p)
  
showInfix
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> Infix p a -> ShowS
showInfix sp sa (Infix p) = sp sa sa p
