{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Infix.Old
  ( module Goat.Syntax.Infix.Old
  , Identity(..)
  )
  where

import Data.Bifunctor
import Data.Coerce (coerce)
import Data.Functor.Identity
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
showWrap sf sa = showParen True . fromWrap sf sa

fromWrap
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Wrap f a -> r
fromWrap kf ka (Wrap fa) = kf ka fa

hoistWrap
 :: (forall x . f x -> g x)
 -> Wrap f a -> Wrap g a
hoistWrap f (Wrap fa) = Wrap (f fa)


data Sum f g a = InL (f a) | InR (g a)
  deriving (Eq, Show, Functor)
  
fromSum
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Sum f g a -> r
fromSum kf kg ka (InL fa) = kf ka fa
fromSum kf kg ka (InR ga) = kg ka ga
  
data Compose f g a = Compose (f (g a))
  deriving (Eq, Show, Functor)
  
fromCompose
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Compose f g a -> r
fromCompose kf kg ka (Compose fga) = kf (kg ka) fga


type Embed f g = Compose f (Sum Identity g)

fromEmbed
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Embed f g a -> r
fromEmbed kf kg = fromCompose kf (fromSum (. runIdentity) kg)

type Op f g = Sum g (Embed f (Wrap g))

showOp
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Op f g a -> ShowS
showOp sf sg =
  fromSum sg (fromEmbed sf (showWrap sg))

fromOp
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Op f g a -> r
fromOp kf kg =
  fromSum kg (fromEmbed kf (fromWrap kg))

newtype Embed f a b = Embed (f (Either a (Wrap b)))
  
data Exp f a  =
    Term (f a)
  | Expr a
  deriving (Eq, Show)

newtype Op p f a =
  Op (p (f (Op p f a)) a)
  deriving (Eq, Show)

newtype Assoc p f a =
  Assoc (Exp (Embed f a)
             (Op p (Embed (Exp f) a)
                   (Either a (Assoc p f a))))
  
  
-- g a ~ p a (Exp f (Exp (g a) b))

-- | An operator 'p',
-- with a possible nested expression type 'f'.
-- The 'a' type represents nested operations of strictly higher precedence.
newtype Assoc p f a =
  Assoc (p (Embed (Sum Identity f) (Wrap (Assoc p f)) a)
           (Sum Identity (Op f (Assoc p f)) a))
-- g a ~ p (((I :+: f) :.: (I :+: Wrap g)) a)
--         ((I :+: (g :+: (f :.: (I :+: Wrap g)))) a)

instance Eq (p (Embed (Sum Identity f) (Wrap (Assoc p f)) a)
               (Sum Identity (Op f (Assoc p f)) a))
 => Eq (Assoc p f a) where
  Assoc pa == Assoc pb = pa == pb
  
instance Show (p (Embed (Sum Identity f) (Wrap (Assoc p f)) a)
                 (Sum Identity (Op f (Assoc p f)) a))
 => Show (Assoc p f a) where
  showsPrec d (Assoc p) = showParen (d>10)
    (showString "Assoc " . showsPrec 11 p)
    
showAssoc
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Assoc p f a -> ShowS
showAssoc sp sf sa (Assoc p) =
  sp (fromEmbed (fromSum (. runIdentity) sf)
                (showWrap (showAssoc sp sf)) sa)
     (fromSum (. runIdentity) (showOp sf (showAssoc sp sf)) sa)
     p

fromAssoc 
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Assoc p f a -> r
fromAssoc kp kf ka (Assoc p) =
  kp (fromEmbed (fromSum (. runIdentity) kf)
                (fromWrap (fromAssoc kp kf)) ka)
     (fromSum (.runIdentity) (fromOp kf (fromAssoc kp kf)) ka)
     p

{-
  
instance Eq (p (m b) a) => Eq (Embed p f a b) where
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
newtype Op p f a =
  Op (FreeF f
            (Embed p f a (FreeF Identity a (Op p f a)))
            (FreeF Wrap
                   a
                   (Embed p f a (FreeF Identity
                                       a
                                       (Op p f a)))))

  
instance
  ( Eq (f (Free (Wrap (Embed p f b)) a))
  , Eq (Embed p f b (Free (Wrap (Embed p f b)) a))
  )
 => Eq (Op p f a b) where
  Term fma == Term fmb = fma == fmb
  Op ea    == Op eb    = ea  == eb
  _        == _        = False
  
instance
  ( Show (f (Free (Wrap (Embed p f b)) a))
  , Show (Embed p f b (Free (Wrap (Embed p f b)) a))
  )
 => Show (Op p f a b) where
  showsPrec d (Term fma) = showParen (d>10)
    (showString "Term " . showsPrec 11 fma)
  showsPrec d (Op eb) = showParen (d>10)
    (showString "Op " . showsPrec 11 eb)

instance (Bifunctor p, Functor f) => Functor (Op p f a) where
  fmap = second

instance (Bifunctor p, Functor f) => Bifunctor (Op p f) where
  bimap f g = bimap' where
    bimap' (Term fm) = Term (fmap ffr fm)
    bimap' (Op em) = Op (bimap g ffr em)
    
    ffr = hoistFree (hoistWrap (first g)) . fmap f

showOp
 :: (Bifunctor p, Functor f)
 => (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Op p f a b -> ShowS
showOp sp sf sa sb = showOp' where
  showOp' (Term fm) = sf sfr fm
  showOp' (Op em) = fromEmbed sp sf sb sfr em
  
  sfr =
    iter (showWrap (fromEmbed sp sf sb) id) . fmap sa

fromOp
 :: (Bifunctor p, Functor f)
 => (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> (b -> r)
 -> Op p f a b -> r
fromOp kp kf ka kb = fromOp' where
  fromOp' (Term fm) = kf kfr fm
  fromOp' (Op em) = fromEmbed kp kf kb kfr em
  
  kfr = iter (fromWrap (fromEmbed kp kf kb) id) . fmap ka

type WrapOp p f a =
    FreeT (Wrap (p a (Free (Bi (Op p f m) a) a))) 
--  Free (Wrap (Embed p f (Free (Bi (Op p f) a) a))) a

-}
  
embedOp
 :: Sum Identity (Op f (Assoc p f)) a
 -> Embed (Sum Identity f) (Wrap (Assoc p f)) a
embedOp (InL a) = Compose (InL (Identity (InL a)))
embedOp (InR (InL ga)) = Compose (InL (Identity (InR (Wrap ga))))
embedOp (InR (InR (Compose fa))) = Compose (InR fa)

infixrOp
 :: (forall x y . x -> y -> p x y)
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
infixrOp op a b =
  InR (InL (Assoc (op (embedOp a) b)))
    
infixlOp
 :: (forall x y . y -> x -> p x y)
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
infixlOp op = infixrOp (flip op)

infixOp
 :: (forall x y . x -> x -> p x y)
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
infixOp op a b =
  InR (InL (Assoc (op (embedOp a) (embedOp b))))

prefixOp
 :: (forall x y . x -> p x y)
 -> Sum Identity (Op f (Assoc p f)) a
 -> Sum Identity (Op f (Assoc p f)) a
prefixOp op a =
  InR (InL (Assoc (op (embedOp a))))
  
  
liftOp
 :: ( forall x
    . Sum Identity f x -> Sum Identity f x -> Sum Identity f x
    )
 -> Sum Identity (Op f g) a
 -> Sum Identity (Op f g) a
 -> Sum Identity (Op f g) a
liftOp lop a b =
  fout (lop (fin a) (fin b))
  where
    -- 'fin' and 'fout' witness an isomorphism between
    -- 'Sum Identity (Op f g) a' and
    -- 'Sum Identity f (Sum Identity g a)'
    fin
     :: Sum Identity (Op f g) a
     -> Sum Identity f (Sum Identity (Wrap g) a)
    fin (InL a) = InL (Identity (InL a))
    fin (InR (InL ga)) = InL (Identity (InR (Wrap ga)))
    fin (InR (InR (Compose fa))) = InR fa
    -- Op f g = Sum g (Embed f (Wrap g))
    -- Embed f g = Compose f (Sum Identity g)
    
    fout
     :: Sum Identity f (Sum Identity (Wrap g) a)
     -> Sum Identity (Op f g) a
    fout (InL (Identity (InL a))) = InL a
    fout (InL (Identity (InR (Wrap ga)))) = InR (InL ga)
    fout (InR fa) = InR (InR (Compose fa))

{-
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


liftOp
 :: Bifunctor q
 => (forall x . Fre q x -> Fre q x -> Fre q x)
 -> Fre (Op p (Assoc q)) a
 -> Fre (Op p (Assoc q)) a
 -> Fre (Op p (Assoc q)) a
liftOp lop a b =
  fout (lop (fin a) (fin b))
  where
    -- 'fin' and 'fout' witness an isomorphism between
    -- 'Fre (Op p (Assoc q)) a' and
    -- 'Fre q (WrapOp p (Assoc q) a)'
    fin
     :: Bifunctor q
     => Fre (Op p (Assoc q)) a
     -> Fre q (WrapOp p (Assoc q) a)
    fin (Fre (Pure a)) = Fre (Pure (Pure a))
    fin (Fre (Free (Bi (Term (Assoc q))))) =
      Fre (Free (fmap unwrapFre (Bi q)))
    -- q :: q (WrapOp p (Assoc q) a)
    --        (Fre q (WrapOp p (Assoc q) a))
    fin (Fre (Free (Bi (Op em)))) = Fre (Pure (Free (Wrap em)))
    -- em :: Embed p (Assoc q)
    --         (Free (Bi (Op p (Assoc q)) a)
    --               (WrapOp p (Assoc q) a))
    --         (WrapOp p (Assoc q) a)
    
    fout
     :: Bifunctor q
     => Fre q (WrapOp p (Assoc q) a)
     -> Fre (Op p (Assoc q)) a
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

-}
