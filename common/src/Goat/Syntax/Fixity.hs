{-# LANGUAGE RankNTypes, UndecidableInstances, DeriveFunctor, FlexibleContexts #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Control.Monad.Free
  
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


--newtype InfixA p a = InfixA (p a (Op (InfixA p) a))
newtype InfixA p m a b = InfixA (p b (m (Op (InfixA p m a) a b)))
--InfixA p m a b ~ p b (FreeT (p b) m a)

instance Eq (p b (m (Op (InfixA p m a) a b)))
 => Eq (InfixA p m a b)
  where
    InfixA pa  == InfixA pb = pa == pb
  
instance Show (p b (m (Op (InfixA p m a) a b)))
 => Show (InfixA p m a b)
  where
    showsPrec i (InfixA p) = showParen (i>10)
      (showString "InfixA " . showsPrec 11 p)
    
instance (Bifunctor p, Functor m) => Functor (InfixA p m a) where
  fmap f (InfixA p) = InfixA (bimap f (fmap (fmap f)) p)
  
instance (Bifunctor p, Functor m) => Bifunctor (InfixA p m) where
  bimap f g (InfixA p) =
    InfixA (bimap g (fmap (hoistOp (first f) . bimap f g))) p

fromInfixL
 :: (forall x y . (x -> r) -> (y -> r) -> p y x -> r)
 -> (forall x . (x -> r) -> m x -> r)
 -> (a -> r) -> (b -> r) -> Op (InfixA p m a) a b -> r
fromInfixL fromp fromm froma fromb = go
  where
    go (Term a) = froma a
    go (Op (InfixA p)) = fromp (fromm go) fromb p

fromInfixR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> m x -> r)
 -> (a -> r) -> (b -> r) -> Op (InfixA p a) a b -> r
fromInfixR fromp fromm froma fromb = go 
  where
    go (Term a) = froma a
    go (Op (InfixA p)) = fromp fromb (fromm go) p

newtype Ex p m a =
  Ex { runEx :: m (Op (InfixA p m a) a (Ex p m a)) }

instance Eq (m (Op (InfixA p m a) a (Ex p m a))) => Eq (Ex p m a)
  where
    Ex ma == Ex mb = ma == mb
    
instance Show (m (Op (InfixA p m a) a (Ex p m a)))
 => Show (Ex p m a)
  where
    showsPrec d (Ex m) = showParen (d>10)
      (showString "Ex " . showsPrec 11 m)
  
instance (Bifunctor p, Monad m) => Functor (Ex p m) where
  fmap f (Ex m) =
    Ex (fmap (hoistOp (first (fmap f)) . bimap f (fmap f)) m)
  
instance (Bifunctor p, Monad m) => Applicative (Ex p m) where
  pure a = Ex (return (Term a))
  (<*>) = ap
  
instance (Bifunctor p, Monad m) => Monad (Ex p m) where
  return = pure
  Ex m >>= f = Ex (m >>= runEx . goOp f)
    where
      go
        :: (a -> Ex p m b)
        -> InfixA p m a (Ex p m a)
        -> InfixA p m b (Ex p m b)
      go f (InfixA p) =
        InfixA (bimap (>>= f) (>>= runEx . goOp f) p)
      
      goOp
        :: (a -> Ex p m b)
        -> Op (InfixA p m a) a (Ex p m a)
        -> Ex p m b
      goOp f (Term a) = f a
      goOp f (Op b) = Ex (return (Op (go f b)))

getTerm :: (a -> r) -> (f b -> r) -> Op f a b -> r
getTerm kp kf (Term a) = kp a
getTerm kp kf (Op f) = kf f

infixL
 :: (InfixA p a b -> a)
 -> (forall x y . x -> y -> p y x)
 -> Op (InfixA p a) a b
 -> Op (InfixA p a) a b
 -> Op (InfixA p a) a b
infixL wrap op a b =
  Op (InfixA (op a (getTerm id wrap b)))
  
infixR
 :: (InfixA p a b -> a)
 -> (forall x y . x -> y -> p x y)
 -> Op (InfixA p a) a b
 -> Op (InfixA p a) a b
 -> Op (InfixA p a) a b
infixR wrap op a b =
  Op (InfixA (op (getTerm id wrap a) b))


{-
instance (Eq a, Eq (p (InfixL p a) a)) => Eq (InfixL p a) where
  TermL a  == TermL b  = a == b
  InfixL pa == InfixL pb = pa == pb
  _         == _         = False
  
instance (Show a, Show (p (InfixL p a) a)) => Show (InfixL p a) where
  showsPrec i (TermL a) = showParen (i>10)
    (showString "TermL " . showsPrec 11 a)
  showsPrec i (InfixL pa) = showParen (i>10)
    (showString "InfixL " . showsPrec 11 pa)

instance Bifunctor p => Functor (InfixL p) where
  fmap f (TermL a) = TermL (f a)
  fmap f (InfixL p) = InfixL (bimap (fmap f) f p)
-}


data InfixR p a =
    TermR a
  | InfixR (p a (InfixR p a))

instance (Eq a, Eq (p a (InfixR p a))) => Eq (InfixR p a) where
  TermR a  == TermR b  = a == b
  InfixR pa == InfixR pb = pa == pb
  _         == _         = False
  
instance (Show a, Show (p a (InfixR p a))) => Show (InfixR p a) where
  showsPrec d (TermR a) = showParen (d > 10)
    (showString "TermR " . showsPrec 11 a)
  showsPrec d (InfixR pa) = showParen (d > 10)
    (showString "InfixR " . showsPrec 11 pa)

instance Bifunctor p => Functor (InfixR p) where
  fmap f (TermR a) = TermR (f a)
  fmap f (InfixR p) = InfixR (bimap f (fmap f) p)


--type Bin p a = Either a (p a a)
newtype Infix p a = Infix (p a a)
{-
data Infix p a =
    TermI a
  | Infix (p a a)
-}
  
fromInfix
  :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
  -> (a -> r) -> Op (Infix p) a a -> r
fromInfix fromp froma (Term a) = froma a
fromInfix fromp froma (Op (Infix p)) =
  fromp froma froma p

infix'
 :: (Infix p a -> a)
 -> (forall x y . x -> y -> p x y)
 -> Op (Infix p) a a
 -> Op (Infix p) a a
 -> Op (Infix p) a a
infix' wrap op a b =
  Op (Infix (op (getTerm id wrap a) (getTerm id wrap b)))

{-
instance (Eq a, Eq (p a a)) => Eq (Infix p a) where
  TermI a  == TermI b  = a == b
  Infix pa == Infix pb = pa == pb
  _        == _        = False
  
instance (Show a, Show (p a a)) => Show (Infix p a) where
  showsPrec d (TermI a) = showParen (d>10) (showString "TermI " . showsPrec 11 a)
  showsPrec d (Infix a) = showParen (d>10) (showString "Infix " . showsPrec 11 a)
-}

instance Bifunctor p => Functor (Infix p) where
  --fmap f (TermI a) = TermI (f a)
  fmap f (Infix p) = Infix (bimap f f p)

{-
data Prefix f a =
    TermP a
  | Prefix (f a)
  deriving (Eq, Show, Functor)
-}
fromPrefix
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r) -> Op f a a -> r
fromPrefix showf showa (Term a) = showa a
fromPrefix showf showa (Op f) = showf showa f

prefix
 :: (f a -> a)
 -> (forall x . x -> f x)
 -> Op f a a
 -> Op f a a
prefix wrap op a = Op (op (getTerm id wrap a))
