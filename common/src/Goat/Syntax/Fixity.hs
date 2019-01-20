{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Free


type Exp = Free

showExp
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Exp f a -> ShowS
showExp sf sa (Pure a) = sa a
showExp sf sa (Free fa) = sf (showExp sf sa) fa
  
newtype Wrap f a = Wrap (f a)
  deriving  (Eq, Show, Functor)
  
showWrap
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Wrap f a -> ShowS
showWrap sf sa (Wrap fa) = showParen True (sf sa fa)
  
data Embed f a b = Embed (f a) | Lift b
  deriving (Eq, Show, Functor)
  
instance Functor f => Bifunctor (Embed f) where
  bimap f g (Embed fa) = Embed (fmap f fa)
  bimap f g (Lift b) = Lift (g b)
  
showEmbed
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Embed f a b -> ShowS
showEmbed sf sa sb (Embed fa) = sf sa fa
showEmbed sf sa sb (Lift b) = sb b


-- |
newtype Op p f a b = Op (p a (Embed f a b))
  deriving (Eq, Show)
--  AssocOp (p (WExp f (AOp p f) a)
--             (AExp f (AOp p f) a))

instance (Bifunctor p, Functor f) => Functor (Op p f a) where
  fmap f (Op p) = Op (bimap f (first f) p)
  
instance (Bifunctor p, Functor f) => Bifunctor (Op p f) where
  bimap f g (Op p) = Op (bimap f (bimap f g) p)

-- | Associative binary operation.
newtype Assoc p f a b = Assoc (Op p f b (Free (Op p f b) a))
  deriving (Eq, Show)
  
instance (Bifunctor p, Functor f) => Functor (Assoc p f a) where
  fmap f (Assoc o) =
    Assoc (bimap f (hoistFree (first f) (fmap g o)))

type WExp p f a = Free (Wrap (Assoc p f)) a
type AExp p f a =
  Embed f (WExp p f a) (Free (Op p f (WExp p f a)) a)

showAExp
 :: (forall x . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> (f x -> ShowS))
 -> (a -> ShowS)
 -> AExp p f a -> ShowS
showAExp sp sf =
  showExp
    (showEOp sf sg (showExp (showWOp sg)))

showWExp
  :: (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (forall x . (x -> ShowS) -> g x -> ShowS)
  -> (a -> ShowS)
  -> WExp f g a -> ShowS
showWExp sf sg =
  showExp
    (showEOp sf (showWOp sg) (showExp (showWOp sg)))

-- | A series of associated operations.
-- 'p' is a binary operation that is associative in its second type argument.
newtype AOp p f a =
  AssocOp (p (WExp f (AOp p f) a)
             (AExp f (AOp p f) a))
-- p (Either (m a) (f (m a)))
--   (Either (Either a b) (f (m a)))

instance Eq (p (WExp f (AOp p f) a) (AExp f (AOp p f) a))
 => Eq (AOp p f a)
  where
    AssocOp pa  == AssocOp pb = pa == pb
 
instance Show (p (WExp f (AOp p f) a) (AExp f (AOp p f) a))
 => Show (AOp p f a)
  where
    showsPrec i (AssocOp p) = showParen (i>10)
      (showString "AssocOp " . showsPrec 11 p)
   
instance (Bifunctor p, Functor f) => Functor (AOp p f) where
  fmap f (AssocOp p) = AssocOp (bimap (fmap f) (fmap f) p)

showAOp
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> AOp p f a -> ShowS
showAOp sp sf sa (AssocOp p) =
  sp (showWExp sf (showAOp sp sf) sa)
     (showAExp sf (showAOp sp sf) sa)
     p

-- newtype Op p f a b = Op (p a (Either (f a) b))
-- newtype Assoc p f a b = Assoc (Op p f b (Free (Op p f b) a))
-- type WExp p f a = Free (Wrap (Assoc p f a)) a
-- type AExp p f a = Either (f (WExp p f a)) (Assoc p f a (WExp p f a))
type AEOp p f = EOp f (AOp p f) (Exp (WOp (AOp p f)))

showAEOp
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> AEOp p f a -> ShowS
showAEOp sp sf sa =
  showEOp
    sf
    (showAOp sp sf)
    (showExp (showWOp (showAOp sp sf)))
    sa
        
    
infixAExp
 :: (forall x y . x -> y -> p x y)
 -> AExp f (AOp p f) a
 -> AExp f (AOp p f) a
 -> AExp f (AOp p f) a
infixAExp op a b =
  Exp (LiftOp (AssocOp (op (f a) b)))
  where
    f :: Exp (EOp f g h) a
      -> Exp (EOp f (WOp g) h) a
    f (Term a) = Term a
    f (Exp (LiftOp aop)) = Exp (LiftOp (WrapOp aop))
    f (Exp (EmbedOp fha)) = Exp (EmbedOp fha)
 
liftAExp
  :: (forall x . Exp f x -> Exp f x -> Exp f x)
  -> Exp (EOp f g (Exp (WOp g))) a
  -> Exp (EOp f g (Exp (WOp g))) a
  -> Exp (EOp f g (Exp (WOp g))) a
liftAExp lop a b =
  fout (lop (fin a) (fin b))
  where
    fin
     :: Exp (EOp f g (Exp (WOp g))) a
     -> Exp f (Exp (WOp g) a)
    fin (Term a) = Term (Term a)
    fin (Exp (LiftOp ga)) = Term (Exp (WrapOp ga))
    fin (Exp (EmbedOp fex)) = Exp fex
    
    fout
     :: Exp f (Exp (WOp g) a)
     -> Exp (EOp f g (Exp (WOp g))) a
    fout (Term (Term a)) = Term a
    fout (Term (Exp (WrapOp ga))) = Exp (LiftOp ga)
    fout (Exp fex) = Exp (EmbedOp fex)
