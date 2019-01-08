{-# LANGUAGE RankNTypes, UndecidableInstances, DeriveFunctor, FlexibleContexts #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Control.Monad.Free
  
data Op f a =
    Term a
  | Op (f a)
  deriving (Eq, Show, Functor)
  
newtype InfixA p a = InfixA (p a (Op (InfixA p) a))

instance (Eq a, Eq (p a (Op (InfixA p) a)))
 => Eq (InfixA p a) where
  InfixA pa  == InfixA pb  = pa == pb
  
instance (Show a, Show (p a (Op (InfixA p) a)))
 => Show (InfixA p a) where
  showsPrec i (InfixA pa) = showParen (i>10)
    (showString "InfixA " . showsPrec 11 pa)
  
instance Bifunctor p => Functor (InfixA p) where
  fmap f (InfixA p) = InfixA (bimap f (fmap f) p)

fromInfixL
 :: (forall x y . (x -> r) -> (y -> r) -> p y x -> r)
 -> (a -> r) -> Op (InfixA p) a -> r
fromInfixL fromp froma (Term a) = froma a
fromInfixL fromp froma (Op (InfixA p)) =
  fromp (fromInfixL fromp froma) froma p

fromInfixR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> Op (InfixA p) a -> r
fromInfixR fromp froma (Term a) = froma a
fromInfixR fromp froma (Op (InfixA p)) =
  fromp froma (fromInfixR fromp froma) p

getTerm :: MonadFree f m => Op f (m a) -> m a
getTerm (Term a) = a
getTerm (Op f) = wrap f

infixL
 :: MonadFree (InfixA p) m
 => (forall x y . x -> y -> p y x)
 -> Op (InfixA p) (m a)
 -> Op (InfixA p) (m a)
 -> Op (InfixA p) (m a)
infixL op a b =
  Op (InfixA (op a (getTerm b)))
  
infixR
 :: MonadFree (InfixA p) m
 => (forall x y . x -> y -> p x y)
 -> Op (InfixA p) (m a)
 -> Op (InfixA p) (m a)
 -> Op (InfixA p) (m a)
infixR op a b =
  Op (InfixA (op (getTerm a) b))


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
  -> (a -> r) -> Op (Infix p) a -> r
fromInfix fromp froma (Term a) = froma a
fromInfix fromp froma (Op (Infix p)) =
  fromp froma froma p

infix'
 :: MonadFree (Infix p) m
 => (forall x y . x -> y -> p x y)
 -> Op (Infix p) (m a)
 -> Op (Infix p) (m a)
 -> Op (Infix p) (m a)
infix' op a b =
  Op (Infix (op (getTerm a) (getTerm b)))

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
 -> (a -> r) -> Op f a -> r
fromPrefix showf showa (Term a) = showa a
fromPrefix showf showa (Op f) = showf showa f

prefix
 :: MonadFree f m
 => (forall x . x -> f x)
 -> Op f (m a) -> Op f (m a)
prefix op a = Op (op (getTerm a))
