{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving, UndecidableInstances #-}
module Goat.Syntax.Infix
  where
  
-- | Denotes a bracketed expression for nesting inside a higher precedence operation.
newtype Wrap a = Wrap a
  deriving  (Eq, Show, Functor)
  
showWrap
 :: (a -> ShowS) -> Wrap a -> ShowS
showWrap sa = showParen True . fromWrap sa

fromWrap
 :: (a -> r) -> Wrap f a -> r
fromWrap ka (Wrap a) = ka a


newtype Embed f a b =
  Embed (f (Either a (Wrap b)))
  deriving (Eq, Show, Functor)
  
showEmbed
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Embed f a b -> ShowS
showEmbed sf sa sb (Embed fe) = sf (either sa (showWrap sb)) fe

fromEmbed
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> (b -> r)
 -> Embed f a b -> r
fromEmbed kf ka kb (Embed fe) = kf (either ka (fromWrap kb)) fe
  
instance Functor f => Bifunctor (Embed f) where
  bimap f g (Embed fe) = Embed (fmap (bimap f (fmap g)) fe)
  

data Exp f a  =
    Term (f a)
  | Expr a
  deriving (Eq, Show, Functor)

hoistExp :: (forall x . f x -> g x) -> Exp f a -> Exp g a
hoistExp f (Term fa) = Term (f fa)
hoistExp _ (Expr a)  = Expr a

fromExp
 :: (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Exp f a -> r
fromExp kf ka (Term fa) = kf ka fa
fromExp kf ka (Expr a) = ka a
  
newtype Op p f a = Op (p (f (Op p f a)) a)

hoistOp
 :: Functor f => (forall x. f x -> g x) -> Op p f a -> Op p g a
hoistOp f (Op p) = Op (first (f . fmap (hoistOp f)) p)

fromOp
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Op p f a -> r
fromOp kp kf ka (Op p) kp (kf (fromOp kp kf ka)) ka p

instance Eq (p (f (Op p f a)) a) => Eq (Op p f a) where
  Op pa == Op pb = pa == pb
  
instance Show (p (f (Op p f a)) a) => Show (Op p f a) where
  showsPrec d (Op pa) = showParen (d>10)
    (showString "Op " . showsPrec 11 pa)
    
instance (Bifunctor p, Functor f) => Functor (Op p f a) where
  fmap f (Op p) = Op (bimap (fmap (fmap f)) f p)

newtype Assoc p f a =
  Assoc (Exp (Embed f a)
             (Op p (Embed (Exp f) a)
                   (Either a (Assoc p f a))))
  deriving (Eq, Show)
     
{-     
instance 
  ( Eq (Embed f a (Op p (Embed (Exp f) a) (Either a (Assoc p f a))))
  , Eq (Op p (Embed (Exp f) a) (Either a (Assoc p f a)))
  ) => Eq (Assoc p f a) where
  Assoc xa == Assoc xb = xa == xb
  
instance
  ( Show (Embed f a (Op (Embed (Exp f) a) (Either a (Assoc p f a))))
  , Show (Op p (Embed (Exp f) a) (Either a (Assoc p f a)))
  ) => Show (Assoc p f a) where
  showsPrec d (Assoc x) = showParen (d>10)
    (showString "Assoc " . showsPrec 11 x)
-}

instance (Bifunctor p, Functor f) => Functor (Assoc p f) where
  fmap f (Assoc x) =
    Assoc (hoistExp (first f)
                    (fmap (hoistOp (first f)
                           . fmap (bimap f (fmap f)))
                          x))

showAssoc
  :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
  -> (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (a -> ShowS)
  -> Assoc p f a -> ShowS)
showAssoc sp sf sa (Assoc x) =
  fromExp (showEmbed sf sa)
          (fromOp sp (showEmbed (fromExp sf) sa)
                     (either sa (showAssoc sp sf sa)))

fromAssoc
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (forall x . (x -> r) -> f x -> r)
 -> (a -> r)
 -> Assoc p f a -> r
fromAssoc kp kf ka (Assoc x) =
  fromExp (fromEmbed kf ka)
          (fromOp kp (fromEmbed (fromExp kf) ka)
                     (either ka (fromAssoc kp kf ka)))


