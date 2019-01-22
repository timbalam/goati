{-# LANGUAGE RankNTypes, DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Goat.Syntax.Fixity
  where
  
import Data.Bifunctor
import Data.Coerce (coerce)
import Control.Monad (ap)
import Control.Monad.Free
import Prelude.Extras

  
-- | Denotes a bracketed expression for nesting inside a higher precedence operation.
newtype Wrap f a = Wrap (f a)
  deriving  (Eq, Eq1, Show, Show1, Functor)
  
showWrap
 :: (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> Wrap f a -> ShowS
showWrap sf sa (Wrap fa) = showParen True (sf sa fa)

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
  
instance (Eq2 p, Bifunctor p, Eq1 f) => Eq2 (Embed p f) where
  Embed pa ==## Embed pb = cp pa == cp pb where
    cp p = Lift2 (first (Lift2 . first Lift1) p)
    
instance (Eq2 p, Bifunctor p, Eq1 f, Eq a)
 => Eq1 (Embed p f a) where
  (==#) = (==##)
  
instance (Eq2 p, Bifunctor p, Eq1 f, Eq a, Eq b)
 => Eq (Embed p f a b) where
  (==) = (==##)
  
instance (Bifunctor p, Functor f) => Functor (Embed p f a) where
  fmap = second
  
instance (Bifunctor p, Functor f) => Bifunctor (Embed p f) where
  bimap f g (Embed p) =
    Embed (bimap (bimap (fmap g) g) f p)
    
showEmbed
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Embed p f a b -> ShowS
showEmbed sp sf sa sb (Embed p) =
  sp (either (sf sb) sb) sa p
  
hoistEmbed
 :: Bifunctor p
 => (forall x . f x -> g x)
 -> Embed p f a b -> Embed p g a b
hoistEmbed f (Embed p) = Embed (first (first f) p)


-- | Interleave an expression type 'f' with expressions involving operator 'p'.
-- Nested occurences of 'p' are in the non-associative position 
-- and are wrapped to indicate precedence.
data Exp p f a b =
    Term (f (Free (Wrap (Embed p f b)) a))
  | Op (Embed p f b (Free (Wrap (Embed p f b)) a))
  
instance (Eq2 p, Bifunctor p, Eq1 f, Functor f)
 => Eq2 (Exp p f) where
  Term fma ==## Term fmb = ct fma == ct fmb where
    ct = Lift1 . fmap Lift1
    
  Op ea ==## Op eb = ce ea == ce eb where
    ce = Lift1 . fmap Lift1
    
  _ ==## _ = False
  
instance (Eq2 p, Bifunctor p, Eq1 f, Functor f, Eq a)
 => Eq1 (Exp p f a) where
  (==#) = (==##)
  
instance (Eq2 p, Bifunctor p, Eq1 f, Functor f, Eq a, Eq b)
 => Eq (Exp p f a b) where
  (==) = (==##)

instance (Bifunctor p, Functor f) => Functor (Exp p f a) where
  fmap = second

instance (Bifunctor p, Functor f) => Bifunctor (Exp p f) where
  bimap f g = bimap' where
    bimap' (Term fm) = Term (fmap ffr fm)
    bimap' (Op em) = Op (bimap g ffr em)
    
    ffr = hoistFree (hoistWrap (first g)) . fmap f

showExp
 :: (Bifunctor p, Functor f)
 => (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Exp p f a b -> ShowS
showExp sp sf sa sb = showExp' where
  showExp' (Term fm) = sf sfr fm
  showExp' (Op em) = showEmbed sp sf sb sfr em
  
  sfr =
    iter (showWrap (showEmbed sp sf sb) id) . fmap sa


infixExp
 :: (forall x y . x -> y -> p x y)
 -> Free (Exp p f a) a
 -> Free (Exp p f a) a
 -> Free (Exp p f a) a
infixExp op a b =
  Free (Op (Embed (op (f a) b)))
  where
    f :: Free (Exp p f a) a
      -> Either
           (f (Free (Wrap (Embed p
                                 f
                                 (Free (Exp p f a) a)))
                     a))
           (Free (Wrap (Embed p
                              f
                              (Free (Exp p f a) a)))
                 a)
    f (Pure a) = Right (Pure a)
    f (Free (Term fm)) = Left fm
    f (Free (Op em)) = Right (Free (Wrap em))

    
newtype Bi f a b = Bi { unwrapBi :: f a b }
  deriving (Eq, Eq1, Eq2, Show, Show1, Show2, Bifunctor)
  
instance Bifunctor f => Functor (Bi f a) where
  fmap = second
  
newtype Fre p a = Fre { unwrapFre :: Free (Bi p a) a }
--  deriving (Eq, Show)

instance Bifunctor p => Functor (Fre p) where
  fmap f (Fre fm) = Fre (hoistFree (first f) (fmap f fm))

-- | Makes a binary operator associative in the second type variable position.
--
-- E.g. For 'data ROp a b = a `Rop` b',
-- 'data LOp a b = b `Lop` a',
-- 'data Op a b = a `Op` a';
-- 'Assoc ROp a' is right-associative,
-- 'Assoc LOp a'  is left-associative,
-- and 'Assoc Op a' is non-associative.
newtype Assoc p a = Assoc (p a (Fre p a))
--  deriving (Eq, Show)
  
instance Bifunctor p => Functor (Assoc p) where
  fmap f (Assoc p) = Assoc (bimap f (fmap f) p)
 

liftExp
 :: (Bifunctor p, Bifunctor q)
 => ( forall x . Fre q x -> Fre q x -> Fre q x )
 -> Fre (Exp p (Assoc q)) a
 -> Fre (Exp p (Assoc q)) a
 -> Fre (Exp p (Assoc q)) a
liftExp lop a b =
  fout (lop (fin a) (fin b))
  where
    fin
     :: (Bifunctor p, Bifunctor q)
     => Fre (Exp p (Assoc q)) a
     -> Fre q 
            (Free (Wrap (Embed p (Assoc q)
                           (Free (Bi (Exp p (Assoc q)) a) a)))
                  a)
    fin (Fre (Pure a)) = Fre (Pure (Pure a))
    fin (Fre (Free (Bi (Term (Assoc q))))) =
      Fre (Free (fmap unwrapFre (Bi q)))
    -- q :: q (Free (Wrap (Embed p (Assoc q)
    --                       (Free (Bi (Exp p (Assoc q)) a) a)))
    --              a)
    --        (Fre q (Free (Wrap (Embed p (Assoc q)  
    --                              (Free (Bi (Exp p (Assoc q)) a) a)))
    --                          a))
    fin (Fre (Free (Bi (Op em)))) = Fre (Pure (Free (Wrap em)))
    -- em :: Embed p (Assoc q) (Free (Exp p (Assoc q) a) b)
    --         (Free (Wrap (Embed p (Assoc q)
    --                        (Free (Exp p (Assoc q) a) a)))
    --               a)
    
    fout
     :: (Bifunctor p, Bifunctor q)
     => Fre q (Free (Wrap (Embed p (Assoc q)
                               (Free (Bi (Exp p (Assoc q)) a) a)))
                    a)
     -> Fre (Exp p (Assoc q)) a
    fout (Fre (Pure (Pure a))) = Fre (Pure a)
    fout (Fre (Pure (Free (Wrap em)))) = Fre (Free (Bi (Op em)))
    fout (Fre (Free q)) =
      Fre (Free (Bi (Term (Assoc (unwrapBi (fmap Fre q))))))

{-    
    funwrap
     :: Free (Wrap (Embed p (Assoc q)
                      (Free (Bi (Exp p (Assoc q)) a) a)))
             a
     -> Free (Bi (Exp p (Assoc q)) a) a
    funwrap (Pure a) = Pure a
    funwrap (Free (Wrap em)) = Free (Bi (Op em))

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

-- | An associative operator expression,
-- with a possible nested expression type 'f'.
-- The 'b' type represents equal-or-higher precedence
-- nested operations,
-- and the 'a' type for nested operations of strictly higher precedence.
newtype ExprOp p f a b =
  ExprOp (Assoc p (Either (f b)) (Either (f b) b) a)
  deriving (Eq, Show)

instance (Bifunctor p, Functor f) => Functor (ExprOp p f a) where
  fmap = second
  
instance (Bifunctor p, Functor f) => Bifunctor (ExprOp p f) where
  bimap f g (ExprOp x) =
    bimap (bimap (fmap f) f)
          g
          (hoistAssoc (first (fmap f)) x)

showExprOp
 :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> ExprOp p f a b -> ShowS
showExprOp sp sf sa sb (ExprOp x) =
  showAssoc sp (either (sf sb)) (either (sf sb) sb) x

-- | A tree of nested expressions interleaved with a functor 'f'.
-- 
-- Makes the associative binary operation recursive in the
-- first type position.
type WrapExp p f a = Free (Wrap (ExprOp p f a)) a

type Exp p f a b =
  Either (f a) (Free (AssocOp p (Either (f a)) (Either (f a) a)) b)
type ExpF p f a b =
  Either (f a) (Assoc p (Either (f a)) (Either (f a) a) b)

showExp
 :: (forall x . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
 -> (forall x . (x -> ShowS) -> f x -> ShowS)
 -> (a -> ShowS)
 -> (b -> ShowS)
 -> Exp p f a b -> ShowS
showExp sp sf sa sb =
  either (sf sa)
    (hoistFree
      (showAssocOp sp (either (sf sa)) (either (sf sa) sa) id)
     . fmap sb)

showWrapExp
  :: (forall x y . (x -> ShowS) -> (y -> ShowS) -> p x y -> ShowS)
  -> (forall x . (x -> ShowS) -> f x -> ShowS)
  -> (a -> ShowS)
  -> WrapExp p f a -> ShowS
showWrapExp sp sf sa =
  iter (showWrap (showExprOp p f a) id) . fmap sa


infixExp
 :: (forall x y . x -> y -> p x y)
 -> Exp p f (WrapExp p f a) a
 -> Exp p f (WrapExp p f a) a
 -> Exp p f (WrapExp p f a) a
infixExp op a b =
  Right (Free (op (fmap f a) b))
  where
    f :: Free (AssocOp p
                       (Either (f (WrapExp p f a)))
                       (Either (f (WrapExp p f a)) (WrapExp p f a)))
              a
      -> Free (WrapExp p f a) a
    f (Pure a) = Pure a
    f (Free o) = Free (Wrap (ExprOp o))
 
liftExp
  :: (forall x . Exp p f g a -> Exp p f g a -> Exp p f g a)
  -> Exp p' (ExpF p f g) g' a
  -> Exp p' (ExpF p f g) g' a
  -> Exp p; (ExpF p f g) g' a
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
-}
