{-# LANGUAGE TypeFamilies, ExistentialQuantification, GeneralizedNewtypeDeriving, RankNTypes #-}
module Goat.Expr.Pattern
  where

import Goat.Lang.Field (Field_(..))
import Goat.Lang.Let (Let_(..))
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Expr.Bindings
import Control.Applicative (liftA2)
import Data.These
import Data.Align
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Semigroup

type IdxBinding f = Set f (NonEmpty Int) (NonEmpty Int)
type IdxPattern f = Pattern (Define f) (IdxBinding f)

data Substitute p f a =
    Result (f a)
  | Substitute
      (p a)
      (Substitute p f (These (NonEmpty Int) a))

instance (Functor p, Functor f) => Functor (Substitute p f) where
  fmap f (Result fa) = Result (fmap f fa)
  fmap f (Substitute p r) =
    Substitute (fmap f p) (fmap (fmap f) r)
  
instance
  (Foldable p, Foldable f) => Foldable (Substitute p f)
  where
    foldMap f (Result fa) = foldMap f fa
    foldMap f (Substitute pa ra) =
      foldMap f pa <> foldMap (foldMap f) ra

instance
  (Traversable p, Traversable f) => Traversable (Substitute p f)
  where
    traverse f (Result fa) = Result <$> traverse f fa
    traverse f (Substitute pa ra) =
      Substitute <$> traverse f pa <*> traverse (traverse f) r

instance (Functor p, Align f) => Align (Substitute p f) where
  nil = Result nil
  
  alignWith f = alignWith' where
    alignWith' (Result fa) (Result fb) =
      Result (alignWith f fa fb)
    alignWith' (Result fa) (Substitute pa rb) =
      Substitute
        (fmap (f . That) pa)
        (alignWith (assocWith f) (Result fa) rb)
    alignWith' (Substitute pa ra) sb =
      Substitute
        (fmap (f . This) pa)
        (alignWith (reassocWith f) ra sb)
      
    reassocWith
     :: (These a b -> c)
     -> These (These (NonEmpty Int) a) b
     -> These (NonEmpty Int) c
    reassocWith f =
      assocWith (f . swap) . swap
    
    assocWith
      :: (These a b -> c)
      -> These a (These (NonEmpty Int) b)
      -> These (NonEmpty Int) c
    assocWith f (This a) = That (f (This a))
    assocWith f (That (This ne)) = This ne
    assocWith f (That (That b)) = That (f (That b))
    assocWith f (That (These ne b)) = These ne (f (That b))
    assocWith f (These a (This ne)) = These ne (f (This a))
    assocWith f (These a (That b)) = That (f (These a b))
    assocWith f (These a (These ne b)) = These ne (f (These a b))
    
    swap :: These a b -> These b a
    swap (This a) = That a
    swap (That b) = This b
    swap (These a b) = These b a

newtype Match r f a =
  Match (These (Pattern r ()) (f a))

data Define r f a =
  forall x .
    Define
      (r x)
      (Substitute (Match (Define r f) f) (Set f x) a)
  deriving (Functor, Foldable, Traversable)

definePattern
 :: These (IdxPattern r f) a
 -> Define r f a
definePattern tha =
  crosswalkPaths
    (zip bs [0..])
    (\ r k -> Define r (Substitute tha' (Result (Set k))))
  where
    (bs, tha') = bitraverse (traverse (\ b -> ([b], ())) pure) tha
    
    crosswalkPaths
     :: (Align r, Align f)
     => [(IdxBinding r f, Int)]
     -> (forall xx .
          r xx -> (xx -> f (NonEmpty Int)) -> p)
     -> p
    crosswalkPaths [] = runC nil
    crosswalkPaths (bn:bns) =
      runC
        (fmap
          foldAlign
          (crosswalkNonEmpty
            (\ (Set f, n) -> f (pure n))
            (bn:|bns)))
        
    foldAlign
     :: (Align f, Semigroup a)
     => NonEmpty (f a) -> f a
    foldAlign = foldr1 (alignWith (<>))
  
    
{-
defineList
 :: (Align r, Traversable r, Semigroup a)
 => [These (IdxPattern r a) b]
 -> Define r a b
defineList ds = crosswalkPaths (zip bs [0..]) (Define ps)
  where 
    (bs, ps) =
      traverse (bitraverse (traverse (\ b -> ([b],()))) pure) ds
          
    crosswalkPaths
     :: (Align r, Semigroup a)
     => [(IdxBinding r a, Int)]
     -> (forall xx . r xx -> (xx -> Visibilities a) -> p)
     -> p
    crosswalkPaths [] = runC nil
    crosswalkPaths (bn:bns) =
      runC
        (fmap foldVisibilities
          (crosswalkNonEmpty
            (\ (b, n) ->
              fmap (either This That) (binding b (pure n)))
            (bn:|bns)))
    
    foldVisibilities
     :: Semigroup a
     => NonEmpty (Visibilities a) -> Visibilities a
    foldVisibilities = foldr1 (<>)
    {-where
        out
         :: Option (Visibilities (WrappedAlign f a))
         -> Maybe (Visibilities (f a))
        out = coerce
          --bimap (fmap unwrapAlign) (fmap unwrapAlign)
        in_
         :: Maybe (Visibilities (f a))
         -> Option (Visibilities (WrappedAlign f a))
        in_ = coerce
          --bimap (fmap WrappedAlign) (fmap WrappedAlign)
    -}
-}

-- missing instance    
crosswalkNonEmpty
 :: Align f => (a -> f b) -> NonEmpty a -> f (NonEmpty b)
crosswalkNonEmpty f (x:|[]) = fmap pure (f x)
crosswalkNonEmpty f (x1:|x2:xs) =
  alignWith cons (f x1) (crosswalkNonEmpty f (x2:|xs)) where
    cons = these pure id (NonEmpty.<|) 

newtype Match a =
  Match { getMatch :: Define SetPattern a }

matchPun
 :: Pun SetPath a -> Match a
matchPun (Pun (SetPath p) a) = SetPath (fmap toPub p) #= a
  where
    toPub = Left . Public . either getPublic getLocal
      
instance IsString a => IsString (Match a) where
  fromString s = matchPun (fromString s)

instance Field_ a => Field_ (Match a) where
  type Compound (Match a) =
    Pun (Reference SetChain) (Compound a)
  p #. k = matchPun (p #. k)

instance Let_ (Match a) where
  type Lhs (Match a) = SetPath
  type Rhs (Match a) = a
  l #= a = Match (These (SetPattern (Bind l)) a)


data Pattern r a =
    Bind a
  | Wild
  | forall x . Decomp (r x) (x -> Pattern r a) (Pattern r a)

instance Functor (Pattern r) where
  fmap f (Bind a) = Bind (f a)
  fmap f Wild = Wild
  fmap f (Decomp r k p) = Decomp r (fmap f . k) (fmap f p)

instance Foldable r => Foldable (Pattern r) where
  foldMap f (Bind a) = f a
  foldMap f Wild = mempty
  foldMap f (Decomp r k p) =
    foldMap (foldMap f . k) r `mappend` foldMap f p

instance Traversable r => Traversable (Pattern r) where
  traverse f (Bind a) = fmap Bind (f a)
  traverse f Wild = pure Wild
  traverse f (Decomp r k p) =
    liftA2
      (\ r p -> Decomp r id p)
      (traverse (traverse f . k) r)
      (traverse f p)

newtype SetPattern =
  SetPattern {
    getPattern ::
      Pattern
        (Define Components (Nested Components (NonEmpty Int))) SetPath
    }

instance IsString SetPattern where
  fromString s = SetPattern (Bind (fromString s))

instance Field_ SetPattern where
  type Compound SetPattern = Reference SetChain
  p #. k = SetPattern (Bind (p #. k))

instance Block_ SetPattern where
  type Stmt SetPattern = Match SetPattern
  block_ bdy =
    SetPattern (Decomp (defineList (in_ bdy)) getPattern Wild)
    where
      in_
       :: [Match a]
       -> [ These
              (IdxPattern
                Components
                (Nested Components (NonEmpty Int)))
              a
          ]
      in_ = 
        fmap (first (fmap getPath . getPattern) . getMatch)

instance Extend_ SetPattern where
  type Ext SetPattern = SetDecomp
  SetPattern p # SetDecomp d = SetPattern (Decomp d getPattern p)
  
newtype SetDecomp =
  SetDecomp {
    getDecomp
     :: Define
          Components
          (Nested Components (NonEmpty Int))
          SetPattern
    }

instance Block_ SetDecomp where
  type Stmt SetDecomp = Match SetPattern
  block_ bdy = SetDecomp (defineList (in_ bdy)) where
    in_
     :: [Match a]
     -> [ These
            (IdxPattern
              Components
              (Nested Components (NonEmpty Int)))
            a
        ]
    in_ = 
      fmap (first (fmap getPath . getPattern) . getMatch)



{-
-- | Wrapper providing a 'Monoid' instance for an 'Align'
newtype WrappedAlign f a =
  WrappedAlign { unwrapAlign :: f a } deriving (Functor, Align)

instance
  (Align f, Semigroup a) => Semigroup (WrappedAlign f a)
  where
    WrappedAlign a <> WrappedAlign b =
      WrappedAlign (alignWith (mergeThese (<>)) a b)
-}
