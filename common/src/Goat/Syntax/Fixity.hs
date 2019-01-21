{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts #-}
--{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Free

  
-- | Denotes a bracketed expression for nesting inside a higher precedence operation.
newtype Wrap f a = Wrap (f a)
  deriving  (Eq, Show, Functor)
  
showWrap
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Wrap f a -> ShowS
showWrap sf sa (Wrap fa) = showParen True (sf sa fa)

-- | Makes a binary operator associative in the second type variable position.
--
-- E.g. For 'data ROp a b = a `Rop` b',
-- 'data LOp a b = b `Lop` a',
-- 'data Op a b = a `Op` a';
-- 'Assoc ROp f a b' is right-associative,
-- 'Assoc LOp f a b'  is left-associative,
-- and 'Assoc Op f a b' is non-associative.
newtype AssocOp p f a b = AssocOp (p a (f b))

instance (Bifunctor p, Functor f) => Functor (Assoc p f a) where
  fmap = second
  
instance (Bifunctor p, Functor f) => Bifunctor (Assoc p f) where
  bimap f g (AssocOp p) =
    AssocOp (bimap f (fmap g) p)

type Assoc p f a b = AssocOp p f a (Free (AssocOp p f a) b)

hoistAssocOp
 :: Bifunctor p
 => (forall x . f x -> g x)
 -> AssocOp p f a b -> AssocOp p g a b
hoistAssocOp f (AssocOp p) = AssocOp (second f p)

hoistAssoc
 :: Bifunctor p
 => (forall x . f x -> g x)
 -> Assoc p f a b -> Assoc p g a b
hoistAssoc f =
  hoistAssoc f . fmap (hoistFree (hoistAssoc f))

showAssocOp
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> AssocOp p f a b -> ShowS
showAssocOp sp sf sa sb (AssocOp p) = sp sa (sf sb) p

showAssoc
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Assoc p f a b -> ShowS
showAssoc sp sf sa sb =
  showAssocOp sp sf sa
    (iter (showAssocOp sp sf sa id) . fmap (sf sb))

-- | Represents a possible layer of a functor 'f' for embedding nested operator expressions.
data Emb f a b = Term a | Emb (f b)
  deriving (Eq, Show, Functor)
  
instance Functor f => Bifunctor (Emb f) where
  bimap f g (Term a) = Term (f a)
  bimap f g (Emb fb) = Emb (fmap g fb)
  
showEmb
  :: (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (a -> ShowS)
  -> (b -> ShowS)
  -> Emb f a b -> ShowS
showEmb sf sa sb (Term a) = sa a
showEmb sf sa sb (Emb fb) = sf sb fb

-- | An associative operator expression,
-- with a possible nested expression type 'f'.
-- The 'b' type represents equal-or-higher precedence
-- nested operations,
-- and the 'a' type for nested operations of strictly higher precedence.
newtype ExprOp p f a b =
  ExprOp (Assoc p (Embed f a) (Embed f b b) b)
  deriving (Eq, Show)

instance (Bifunctor p, Functor f) => Functor (ExprOp p f a) where
  fmap = second
  
instance (Bifunctor p, Functor f) => Bifunctor (ExprOp p f) where
  bimap f g (ExprOp x) =
    bimap (bimap g g)
          g
          (hoistAssoc (first f) x)

showExprOp
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> ExprOp p f a b -> ShowS
showExprOp sp sf sa sb (ExprOp x) =
  showAssoc sp (showEmb sf sb sb) (showEmb sf sa sb) x

-- | An expression tree with possibly nested expressions embedded in a functor 'f'.
-- 
-- Makes the associative binary operation recursive in the
-- first type position.
type Exp p f a =
  Embed f a
    (Free (p (Embed f (WrapExp p f a) (WrapExp p f a)))
          (Embed f a (WrapExp p f a)))
          
-- AssocOp p f a (Free (AssocOp p f a) b)
-- p (Embed f (WrapExp p f a') (WrapExp p f a'))
--   (Embed f a'
--     (Free (AssocOp p (Embed f a')
--              (Embed f (WrapExp p f a') (WrapExp p f a')))
--           (WrapExp p f a')))
          
  Free (p (Embed f (WrapExp p f a) (WrapExp p f a)))
       (Embed f a (WrapExp p f a)))
type WrapExp p f a = Free (Wrap (ExprOp p f a)) a

type ExpA p f a =
  Either (p (Embed f (WrapExp p f a) (WrapExp p f a))
            (Exp p f a))
         (f (WrapExp p f a))



type WrapExp p f a = Free (Wrap (Assoc p a) a)
Op p (Emb f a (Free (Op p (Emb f a)) a))


type WrapExp p f a = Free (Wrap (Assoc p f a)) a
type ExpOp p f a =
  Either (f (WrapExp p f a))
         (Assoc p f a (WrapExp p f a))
         
type Exp p f a =
  Either (f (WrapExp p f a))
         (Free (Op p f (WrapExp p f a)) a)
-- FreeT (Op p f (WrapExp p f a))
--       (Either (f (WrapExp p f a)))
--       a

showExpOp
 :: (forall x . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> (f x -> ShowS))
 -> (a -> ShowS)
 -> ExpOp p f a -> ShowS
showExpOp sp sf sa =
  either
    (sf (showWrapExp sp sf sa))
    (showAssoc sp sf sa (showWrapExp sp sf sa))

showWrapExp
  :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
  -> (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (a -> ShowS)
  -> WrapExp p f a -> ShowS
showWrapExp sp sf sa =
  iter (showWrap (showAssoc p f a) id) . fmap sa
        
    
infixExp
 :: (forall x y . x -> y -> p x y)
 -> Exp p f a
 -> Exp p f a
 -> Exp p f a
infixExp op a b =
  Right (Free (op (fmap f a) b))
  where
    f :: Free (Op p f (WrapExp p f a)) a
      -> Free (Wrap (Assoc p f a)) a
      -- Exp (EOp f (WOp g) h) a
    f (Pure a) = Pure a
    f (Free o) = Free (Wrap (Assoc o))
 
liftExp
  :: (forall x . Either ( x) (g -> Free f x -> Free f x)
  -> Either (f (WrapExp p f a))
            (Free (Op p f (WrapExp p f a)) a)
  -> Exp p f a
  -> Exp p f a
liftExp lop a b =
  fout (lop (fin a) (fin b))
  where
    fin
     :: Either (f (WrapExp p f a))
               (Free (Op p f (WrapExp p f a)) a)
        -- Exp (EOp f g (Exp (WOp g))) a
     -> Free f (Free (Wrap (Assoc p f a)) a)
        -- Exp f (Exp (WOp g) a)
    fin (Right (Pure a)) = Pure (Pure a)
    -- fin (Term a) = Term (Term a)
    fin (Right (Free o)) = Pure (Free (Wrap (Assoc o)))
    -- fin (Exp (LiftOp ga)) = Term (Exp (WrapOp ga))
    fin (Left fex) = Free fex
    fin (Exp (EmbedOp fex)) = Exp fex
    
    fout
     :: Exp f (Exp (WOp g) a)
     -> Exp (EOp f g (Exp (WOp g))) a
    fout (Term (Term a)) = Term a
    fout (Term (Exp (WrapOp ga))) = Exp (LiftOp ga)
    fout (Exp fex) = Exp (EmbedOp fex)
