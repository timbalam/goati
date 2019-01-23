{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Infix
  where

import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Free
--import Prelude.Extras

  
-- | Denotes a bracketed expression for nesting inside a higher precedence operation.
newtype Wrap f a = Wrap (f a)
  deriving  (Eq, Show, Functor)
  
showWrap
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Wrap f a -> ShowS
showWrap sf sa (Wrap fa) = showParen True (sf sa fa)

fromWrap
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Wrap f a -> r
fromWrap kf ka (Wrap fa) = kf ka fa

hoistWrap
 :: (forall x . f x -> g x)
 -> Wrap f a -> Wrap g a
hoistWrap f (Wrap fa) = Wrap (f fa)


-- | An operator 'p',
-- with a possible nested expression type 'f'.
-- The 'a' type represents associative nested operations,
-- and the 'b' type for nested operations of strictly higher precedence.
newtype Embed p f a b =
  Embed (p (Either (f b) b) a)
  
instance Eq (p (Either (f b) b) a) => Eq (Embed p f a b) where
  Embed pa == Embed pb = pa == pb
  
instance Show (p (Either (f b) b) a) => Show (Embed p f a b) where
  showsPrec d (Embed p) = showParen (d>10)
    (showString "Embed " . showsPrec 11 p)
  
instance (Bifunctor p, Functor f) => Functor (Embed p f a) where
  fmap = second
  
instance (Bifunctor p, Functor f) => Bifunctor (Embed p f) where
  bimap f g (Embed p) =
    Embed (bimap (bimap (fmap g) g) f p)

fromEmbed
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> (b -> r)
 -> Embed p f a b -> r
fromEmbed kp kf ka kb (Embed p) =
  kp (either (kf kb) kb) ka p

hoistEmbed
 :: Bifunctor p
 => (forall x . f x -> g x)
 -> Embed p f a b -> Embed p g a b
hoistEmbed f (Embed p) = Embed (first (first f) p)


-- | Interleave an expression type 'f' with expressions involving operator 'p'.
-- Nested occurences of 'p' are in the non-associative position 
-- and are wrapped to indicate precedence.
data Infix p f a b =
    Term (f (Free (Wrap (Embed p f b)) a))
  | Op (Embed p f b (Free (Wrap (Embed p f b)) a))
  
instance
  ( Eq (f (Free (Wrap (Embed p f b)) a))
  , Eq (Embed p f b (Free (Wrap (Embed p f b)) a))
  )
 => Eq (Infix p f a b) where
  Term fma == Term fmb = fma == fmb
  Op ea    == Op eb    = ea  == eb
  _        == _        = False
  
instance
  ( Show (f (Free (Wrap (Embed p f b)) a))
  , Show (Embed p f b (Free (Wrap (Embed p f b)) a))
  )
 => Show (Infix p f a b) where
  showsPrec d (Term fma) = showParen (d>10)
    (showString "Term " . showsPrec 11 fma)
  showsPrec d (Op eb) = showParen (d>10)
    (showString "Op " . showsPrec 11 eb)

instance (Bifunctor p, Functor f) => Functor (Infix p f a) where
  fmap = second

instance (Bifunctor p, Functor f) => Bifunctor (Infix p f) where
  bimap f g = bimap' where
    bimap' (Term fm) = Term (fmap ffr fm)
    bimap' (Op em) = Op (bimap g ffr em)
    
    ffr = hoistFree (hoistWrap (first g)) . fmap f

showInfix
 :: (Bifunctor p, Functor f)
 => (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Infix p f a b -> ShowS
showInfix sp sf sa sb = showInfix' where
  showInfix' (Term fm) = sf sfr fm
  showInfix' (Op em) = fromEmbed sp sf sb sfr em
  
  sfr =
    iter (showWrap (fromEmbed sp sf sb) id) . fmap sa

fromInfix
 :: (Bifunctor p, Functor f)
 => (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> (b -> r)
 -> Infix p f a b -> r
fromInfix kp kf ka kb = fromInfix' where
  fromInfix' (Term fm) = kf kfr fm
  fromInfix' (Op em) = fromEmbed kp kf kb kfr em
  
  kfr = iter (fromWrap (fromEmbed kp kf kb) id) . fmap ka

type WrapInfix p f a =
  Free (Wrap (Embed p f (Free (Bi (Infix p f) a) a))) a
  
embedFre
 :: Fre (Infix p f) a
 -> Either (f (WrapInfix p f a)) (WrapInfix p f a)
embedFre (Fre (Pure a)) = Right (Pure a)
embedFre (Fre (Free (Bi (Term fm)))) = Left fm
embedFre (Fre (Free (Bi (Op em)))) = Right (Free (Wrap em))

makeInfixr
 :: (forall x y . x -> y -> p x y)
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
makeInfixr op a b =
  Fre (Free (Bi (Op (Embed (op (embedFre a) (unwrapFre b))))))
    
makeInfixl
 :: (forall x y . y -> x -> p x y)
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
makeInfixl op = infixR (flip op)

makeInfix
 :: (forall x y . x -> x -> p x y)
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
makeInfix op a b =
  Fre (Free (Bi (Op (Embed (op (embedFre a) (embedFre b))))))

makePrefix
 :: (forall x y . x -> p x y)
 -> Fre (Infix p f) a
 -> Fre (Infix p f) a
makePrefix op a =
  Fre (Free (Bi (Op (Embed (op (embedFre a))))))

-- | Makes a binary operator associative in the second type variable position.
--
-- E.g. For 'data ROp a b = a `Rop` b',
-- 'data LOp a b = b `Lop` a',
-- 'data Op a b = a `Op` a';
-- 'Assoc ROp a' is right-associative,
-- 'Assoc LOp a'  is left-associative,
-- and 'Assoc Op a' is non-associative.
newtype Assoc p a = Assoc (p a (Fre p a))

instance Eq (p a (Fre p a)) => Eq (Assoc p a) where
  Assoc pa == Assoc pb = pa == pb
  
instance Show (p a (Fre p a)) => Show (Assoc p a) where
  showsPrec d (Assoc p) = showParen (d>10)
    (showString "Assoc " . showsPrec 11 p)
  
instance Bifunctor p => Functor (Assoc p) where
  fmap f (Assoc p) = Assoc (bimap f (fmap f) p)

fromAssoc
 :: Bifunctor p
 => (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r)
 -> Assoc p a -> r
fromAssoc kp ka (Assoc p) = kp ka (fromFre kp ka) p


liftInfix
 :: Bifunctor q
 => (forall x . Fre q x -> Fre q x -> Fre q x)
 -> Fre (Infix p (Assoc q)) a
 -> Fre (Infix p (Assoc q)) a
 -> Fre (Infix p (Assoc q)) a
liftInfix lop a b =
  fout (lop (fin a) (fin b))
  where
    -- 'fin' and 'fout' witness an isomorphism between
    -- 'Fre (Infix p (Assoc q)) a' and
    -- 'Fre q (WrapInfix p (Assoc q) a)'
    fin
     :: Bifunctor q
     => Fre (Infix p (Assoc q)) a
     -> Fre q (WrapInfix p (Assoc q) a)
    fin (Fre (Pure a)) = Fre (Pure (Pure a))
    fin (Fre (Free (Bi (Term (Assoc q))))) =
      Fre (Free (fmap unwrapFre (Bi q)))
    -- q :: q (WrapInfix p (Assoc q) a)
    --        (Fre q (WrapInfix p (Assoc q) a))
    fin (Fre (Free (Bi (Op em)))) = Fre (Pure (Free (Wrap em)))
    -- em :: Embed p (Assoc q)
    --         (Free (Bi (Infix p (Assoc q)) a)
    --               (WrapInfix p (Assoc q) a))
    --         (WrapInfix p (Assoc q) a)
    
    fout
     :: Bifunctor q
     => Fre q (WrapInfix p (Assoc q) a)
     -> Fre (Infix p (Assoc q)) a
    fout (Fre (Pure (Pure a))) = Fre (Pure a)
    fout (Fre (Pure (Free (Wrap em)))) = Fre (Free (Bi (Op em)))
    fout (Fre (Free q)) =
      Fre (Free (Bi (Term (Assoc (unwrapBi (fmap Fre q))))))

    
-- | Wrapper types
newtype Bi f a b = Bi { unwrapBi :: f a b }
  deriving (Eq, Show, Bifunctor)
  
instance Bifunctor f => Functor (Bi f a) where
  fmap = second
  
fromBi
 :: (forall x y . (x -> r) -> (y -> r) -> f x y -> r)
 -> (a -> r)
 -> (b -> r)
 -> Bi f a b -> r
fromBi kf ka kb (Bi fab) = kf ka kb fab


newtype Fre p a = Fre { unwrapFre :: Free (Bi p a) a }

instance Eq (Free (Bi p a) a) => Eq (Fre p a) where
  Fre fa == Fre fb = fa == fb
  
instance Show (Free (Bi p a) a) => Show (Fre p a) where
  showsPrec d (Fre m) = 
    showString "Fre {unwrapFre = "
    . shows m
    . showString "}"

instance Bifunctor p => Functor (Fre p) where
  fmap f (Fre fm) = Fre (hoistFree (first f) (fmap f fm))
  
fromFre
 :: Bifunctor p
 => (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r)
 -> Fre p a -> r
fromFre kp ka (Fre m) = iter (fromBi kp ka id) (fmap ka m)
