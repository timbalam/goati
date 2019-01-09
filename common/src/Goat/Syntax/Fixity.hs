{-# LANGUAGE RankNTypes, UndecidableInstances, DeriveFunctor, FlexibleContexts #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
  
data Op f a b =
    Term a
  | Op (f b)
  deriving (Eq, Show, Functor)
  
instance Functor f => Bifunctor (Op f) where
  bimap f g (Term a) = Term (f a)
  bimap f g (Op fb) = Op (fmap g fb)

--newtype InfixA p a = InfixA (p a (Op (InfixA p) a))
newtype InfixA p a b = InfixA (p b (Op (InfixA p a) a b))

instance (Eq (p b (Op (InfixA p a) a b)))
 => Eq (InfixA p a b) where
  InfixA pa  == InfixA pb  = pa == pb
  
instance (Show (p b (Op (InfixA p a) a b)))
 => Show (InfixA p a b) where
  showsPrec i (InfixA pa) = showParen (i>10)
    (showString "InfixA " . showsPrec 11 pa)
    
instance Bifunctor p => Functor (InfixA p a) where
  fmap f (InfixA p) = InfixA (bimap f (fmap f) p)

fromInfixL
 :: (forall x y . (x -> r) -> (y -> r) -> p y x -> r)
 -> (a -> r) -> (b -> r) -> Op (InfixA p a) a b -> r
fromInfixL fromp froma fromb (Term a) = froma a
fromInfixL fromp froma fromb (Op (InfixA p)) =
  fromp (fromInfixL fromp froma fromb) fromb p

fromInfixR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> (b -> r) -> Op (InfixA p a) a b -> r
fromInfixR fromp froma fromb (Term a) = froma a
fromInfixR fromp froma fromb (Op (InfixA p)) =
  fromp fromb (fromInfixR fromp froma fromb) p

newtype Ex p m a = Ex (FreeT (p a) m a)
  deriving (Eq, Show)
  
instance (Bifunctor p, Monad m) => Functor (Ex p m) where
  fmap f (Ex m) = Ex (transFreeT (first f) (fmap f m))
  
instance (Bifunctor p, Monad m) => Applicative (Ex p m) where
  pure a = Ex (pure a)
  (<*>) = ap
  
instance (Bifunctor p, Monad m) => Monad (Ex p m) where
  return = pure
  Ex m >>= f = go m where
    go (FreeT m) = m >>= \ a -> case a of
      Pure a -> f a
      Free p -> 

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
