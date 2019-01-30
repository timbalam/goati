{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving, StandaloneDeriving, UndecidableInstances #-}
module Goat.Syntax.Infix
  where
  
import Data.Bifunctor


-- | Inject a higher precedence term 'a' into an operator expression 'b'.
data Term a b =
    Term a
  | Op b
  deriving (Eq, Show, Functor)
  
fromTerm
  :: (a -> r) -> (b -> r) -> Term a b -> r
fromTerm ka kb (Term a) = ka a
fromTerm ka kb (Op b) = kb b

instance Bifunctor Term where
  bimap f g (Term a) = Term (f a)
  bimap f g (Op b) = Op (g b)
  

-- | An expression involving an associative operator type 'p',
-- and a terminal value 'a'.
-- Operator type 'p' has kind '* -> * -> *'.
-- The constructed type 'Assoc p a' augments 'p' with "wrapped" nested operations in the first type position,
-- and unwrapped nested operations in the second "associative" position.
--
-- E.g.
-- 'data Add a b = b :+ a'
-- 'data Mul a b = b :* a' 
-- 'Assoc (Left a :+ Left a) :: Assoc Add a'
-- 'Assoc (Left a :+ Right (Assoc (Left a :+ Left a))) :: Assoc Add a'
-- 'Assoc (Right (Parens (Assoc (Left a :* Left a)) :* Left a) :: Assoc Mul a'
newtype Assoc p a =
  Assoc (p (Either a (Parens (Assoc p a)))
           (Either a (Assoc p a)))

deriving instance
    Eq (p (Either a (Parens (Assoc p a))) (Either a (Assoc p a)))
 => Eq (Assoc p a)

deriving instance
    Show (p (Either a (Parens (Assoc p a))) (Either a (Assoc p a)))
 => Show (Assoc p a)

instance Bifunctor p => Functor (Assoc p) where
  fmap f (Assoc p) =
    Assoc
      (bimap
        (bimap f (fmap (fmap f)))
        (bimap f (fmap f))
        p)

showAssoc
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (a -> ShowS)
 -> Assoc p a -> ShowS
showAssoc sp sa (Assoc p) =
  sp
    (either sa (showParens (showAssoc sp sa)))
    (either sa (showAssoc sp sa))
    p
        
fromAssoc
 :: (forall x y . (x -> r) -> (y -> r) -> p x y -> r)
 -> (a -> r)
 -> Assoc p a -> r
fromAssoc kp ka (Assoc p) =
  kp
    (either ka (fromParens (fromAssoc kp ka)))
    (either ka (fromAssoc kp ka))
    p


-- | Augment terms of lower precedence expression 'g' with "wrapped" terms of higher precedence expression 'f'.
-- For example, if 'Assoc Mul a' is the type of expressions involving multiplication,
-- and 'Assoc Add a' is the type of expressions involving addition,
-- then 'Embed (Assoc Add) (Assoc Mul) a' is the type of expressions involving
-- multiplication with nested wrapped addition expressions.
-- 
-- E.g. 
-- 'Embed (Assoc (Term (Left a) :* Term (Left a))) :: Embed f (Assoc Mul) a'
-- 'Embed (Assoc (Term (Right (Parens (Assoc (Term (Left a) :+ Term (Left a))))))) :: Embed (Assoc Add) (Assoc Mul) a
newtype Embed f g a =
  Embed (g (Either a (Parens (f (Either a (Embed f g a))))))

deriving instance 
    Show (g (Either a (Parens (f (Either a (Embed f g a))))))
 => Show (Embed f g a)

deriving instance
    Eq (g (Either a (Parens (f (Either a (Embed f g a))))))
 => Eq (Embed f g a)

instance (Functor f, Functor g) => Functor (Embed f g) where
  fmap f (Embed ge) =
    Embed
      (fmap 
        (bimap f (fmap (fmap (bimap f (fmap f)))))
        ge)
  
showEmbed
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Embed f g a -> ShowS
showEmbed sf sg sa (Embed fe) =
  sg
    (either
      sa
      (showParens
        (sf (either sa (showEmbed sf sg sa)))))
    fe

fromEmbed
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Embed f g a -> r
fromEmbed kf kg ka (Embed fe) =
  kg
    (either
      ka
      (fromParens 
        (kf (either ka (fromEmbed kf kg ka)))))
    fe

-- | An combined expression involving terms of higher precedence expression 'f' and lower precedence expression 'g',
-- with terminal expressions of type 'a'.
newtype Expr f g a =
  Expr (Either (Embed f g a) (f (Either a (Embed f g a))))
  
deriving instance
    Eq (Either (Embed f g a) (f (Either a (Embed f g a))))
 => Eq (Expr f g a)
 
deriving instance
    Show (Either (Embed f g a) (f (Either a (Embed f g a))))
 => Show (Expr f g a)
 
instance (Functor f, Functor g) => Functor (Expr f g) where
  fmap f (Expr t) =
    Expr (bimap (fmap f) (fmap (bimap f (fmap f))) t)

showExpr
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (forall x . (x -> ShowS) -> g x -> ShowS)
 -> (a -> ShowS)
 -> Expr f g a -> ShowS
showExpr sf sg sa (Expr t) =
  either
    (showEmbed sf sg sa)
    (sf (either sa (showEmbed sf sg sa)))
    t

fromExpr
 :: (forall x . (x -> r) -> f x -> r)
 -> (forall x . (x -> r) -> g x -> r)
 -> (a -> r)
 -> Expr f g a -> r
fromExpr kf kg ka (Expr t) =
  either
    (fromEmbed kf kg ka)
    (kf (either ka (fromEmbed kf kg ka)))
    t


-- | Lift operations to expressions.
infixrOp
 :: (forall x y . x -> y -> p x y)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
infixrOp op a b =
  Right (Assoc (op (fmap Parens a) b))
    
infixlOp
 :: (forall x y . y -> x -> p x y)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
infixlOp op a b =
  Right (Assoc (op a (fmap Parens b)))

infixOp
 :: (forall x y . x -> x -> p x y)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
infixOp op a b =
  Right (Assoc (op (fmap Parens a) (fmap Parens b)))

prefixOp
 :: (forall x y . x -> p x y)
 -> Either a (Assoc p a)
 -> Either a (Assoc p a)
prefixOp op a =
  Right (Assoc (op (fmap Parens a)))


lowerOp
 :: (forall x . Either x (f x) -> Either x (f x) -> Either x (f x))
 -> Either a (Expr f g a)
 -> Either a (Expr f g a)
 -> Either a (Expr f g a)
lowerOp fop a b =
  fout (fop (fin a) (fin b))
  where
    -- 'fin' and 'fout' witness an isomorphism between
    -- 'Either a (Exp f g a)' and
    -- 'Either (Either a (Embed f g a))
    --         (f (Either a (Embed f g a)))'
    fin
     :: Either a (Expr f g a)
     -> Either (Either a (Embed f g a)) (f (Either a (Embed f g a)))
    fin (Left a) = Left (Left a)
    fin (Right (Expr (Right fa))) = Right fa
    fin (Right (Expr (Left e))) = Left (Right e)
    
    fout
     :: Either (Either a (Embed f g a)) (f (Either a (Embed f g a)))
     -> Either a (Expr f g a)
    fout (Left (Left a)) = Left a
    fout (Left (Right e)) = Right (Expr (Left e))
    fout (Right fa) = Right (Expr (Right fa))

liftOp
 :: (forall x . Either x (g x) -> Either x (g x) -> Either x (g x))
 -> Either a (Expr f g a)
 -> Either a (Expr f g a)
 -> Either a (Expr f g a)
liftOp fop a b =
  fout (fop (fin a) (fin b))
  where
    -- 'fin' and 'fout' witness an isomorphism between
    -- 'Either a (Exp f g a)' and
    -- 'Either (Either a (Parens (f (Either a (Embed f g a)))))
    --         (g (Either a (Parens (f (Either a (Embed f g a))))))'
    fin
     :: Either a (Expr f g a)
     -> Either
          (Either a (Parens (f (Either a (Embed f g a)))))
          (g (Either a (Parens (f (Either a (Embed f g a))))))
    fin (Left a) = Left (Left a)
    fin (Right (Expr (Left (Embed ga)))) = Right ga
    fin (Right (Expr (Right fa))) = Left (Right (Parens fa))
    
    fout
     :: Either
          (Either a (Parens (f (Either a (Embed f g a)))))
          (g (Either a (Parens (f (Either a (Embed f  g a))))))
     -> Either a (Expr f g a)
    fout (Left (Left a)) = Left a
    fout (Left (Right (Parens ga))) = Right (Expr (Right ga))
    fout (Right fa) = Right (Expr (Left (Embed fa)))


-- | Denotes a bracketed expression for nesting inside a higher precedence operation.
newtype Parens a = Parens a
  deriving (Eq, Show, Functor)

showParens
 :: (a -> ShowS) -> Parens a -> ShowS
showParens sa = showParen True . fromParens sa

fromParens
 :: (a -> r) -> Parens a -> r
fromParens ka (Parens a) = ka a
