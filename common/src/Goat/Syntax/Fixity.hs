{-# LANGUAGE RankNTypes, UndecidableInstances, DeriveFunctor #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
  
newtype InfixA p a = InfixA (Free (p a) a)
  deriving (Eq, Show)
  
instance Bifunctor p => Functor (InfixA p) where
  fmap f (InfixA m) = InfixA (hoistFree (first f) (fmap f m))

fromInfixL
 :: (forall x y . (x -> r) -> (y -> r) -> p y x -> r)
 -> (a -> r) -> InfixA p a -> r
fromInfixL fromp froma (InfixA m) = iter (fromp id froma) (fmap froma m)
{-
fromInfixL fromp froma (TermL a) = froma a
fromInfixL fromp froma (InfixL p) =
  fromp (fromInfixL fromp froma) froma p
-}

infixL
 :: MonadFree (p (m a)) m
 => (forall x y . x -> y -> p y x)
 -> InfixA p (m a) -> InfixA p (m a) -> InfixA p (m a)
infixL op (InfixA a) (InfixA b) = InfixA (Free (op a (getp b)))
  where
    getp (Pure m) = m
    getp (Free p) = wrap p
    
  
fromInfixR
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r) -> InfixA p a -> r
fromInfixR fromp froma (InfixA m) = iter (fromp froma id) (fmap froma m)
  
infixR
 :: MonadFree (p (m a)) m
 => (forall x y . x -> y -> p x y)
 -> InfixA p a -> InfixA p a -> InfixA p a
infixR op (InfixA a) (InfixA b) = InfixA (Free (op (getp a) b))
  where
    getp (Pure m) = m
    getp (Free p) = wrap p

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


data Infix p a =
    TermI a
  | Infix (p a a)
  
fromInfix
  :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
  -> (a -> r) -> Infix p a -> r
fromInfix fromp froma (TermI a) = froma a
fromInfix fromp froma (Infix p) = fromp froma froma p

infix
 :: MonadFree (Infix p) m
 => (forall x y . x -> y -> p x y)
 -> Infix p a -> Infix p a -> Infix p a
infix op a b = Infix (op (getp a) (getp b))
  where
    getp (TermI a) = a
    getp a         = wrap a

instance (Eq a, Eq (p a a)) => Eq (Infix p a) where
  TermI a  == TermI b  = a == b
  Infix pa == Infix pb = pa == pb
  _        == _        = False
  
instance (Show a, Show (p a a)) => Show (Infix p a) where
  showsPrec d (TermI a) = showParen (d>10) (showString "TermI " . showsPrec 11 a)
  showsPrec d (Infix a) = showParen (d>10) (showString "Infix " . showsPrec 11 a)

instance Bifunctor p => Functor (Infix p) where
  fmap f (TermI a) = TermI (f a)
  fmap f (Infix p) = Infix (bimap f f p)


data Prefix f a =
    TermP a
  | Prefix (f a)
  deriving (Eq, Show, Functor)

fromPrefix
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r) -> Prefix f a -> r
fromPrefix showf showa (TermP a) = showa a
fromPrefix showf showa (Prefix f) = showf showa f


prefix
 :: MonadFree (Prefix f) m
 => (forall x . x -> f x)
 -> Prefix f a -> Prefix f a
prefix op a = Prefix (op (getf a))
  where 
    getf (TermP a) = a
    getf a         = wrap a

