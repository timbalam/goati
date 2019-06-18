{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, FlexibleContexts #-}

-- | This module implements some data types and definitions for represent Goat values that track errors dynamically.
-- It defines a data type 'Dyn': a wrapper for injecting dynamic errors inside a storage type.

module Goat.Repr.Dyn where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Util ((<&>))
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bitraverse)
import Data.Discrimination
  (runGroup, Grouping(..), nubWith)
import Data.Foldable (traverse_)
import Data.Functor.Identity (runIdentity)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import qualified Data.Text as Text
import Prelude.Extras (Eq1(..), Show1(..))


data DynCpts e a b
  = DynCpts (Assocs (,) (Either e) a b) (Maybe e)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance (Eq e, Eq a) => Eq1 (DynCpts e a)
instance (Show e, Show a) => Show1 (DynCpts e a)

checkComponents
 :: (Grouping k, Monoid m)
 => (m -> e)
 -> (a -> ([e], b))
 -> AnnCpts m k a 
 -> ([e], DynCpts e k b)
checkComponents throwe f (Assocs ps)
  = foldMap id
      (zipWith
        (\ (k, _) tups
         -> Assocs . pure . (,) k
         <$> checkDuplicates (f . runIdentity)
              (throwe
                (foldMap (\ (ts, _, _) -> ts) ps))
              tups)
        (nubWith fst crumbps)
        (runGroup grouping crumbps))
 <&> (`DynCpts` Nothing)
  where
  crumbps
    = [(k, (t, a)) | (t, k, a) <- ps]
  
  checkDuplicates 
   :: (a -> ([e], b))
   -> e
   -> [(t, a)]
   -> ([e], Either e b)
  checkDuplicates f _e [(_, a)]
    = Right <$> f a
  
  checkDuplicates f e ps
    = traverse_ (f . snd) ps >> ([e], Left e)

throwDyn :: e -> DynCpts e a b
throwDyn e = DynCpts mempty (Just e)  

-- | Dynamic errors

mapError
 :: (e -> e')
 -> DynCpts e a b -> DynCpts e' a b
mapError f (DynCpts ascs me)
  = DynCpts (hoistAssocs (first f) ascs) (f <$> me)

displayDynCpts
 :: (e -> String)
 -> (a -> String)
 -> DynCpts e a b -> String
displayDynCpts showe showk (DynCpts (Assocs ps) me)
  = "components: "
 ++ show (map (showk . fst) ps)
 ++ maybe "" (showString "," . showe) me
