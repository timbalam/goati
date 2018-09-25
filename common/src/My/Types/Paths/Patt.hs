{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module My.Types.Paths.Patt
  ( module My.Types.Paths.Patt
  , module My.Types.Paths.Tup
  )
  where
  
  
import qualified My.Types.Syntax.Class as S
import My.Types.Paths.Tup
import My.Util (Compose(..), showsUnaryWith)
import Control.Comonad.Cofree
import Data.Functor.Identity
import Prelude.Extras

      
-- | Pattern
type Patt f = Cofree (Decomp f)
newtype Decomp f a = Decomp { getDecomp :: [f a] }
  deriving (Functor, Foldable, Traversable)
  
instance Eq1 f => Eq1 (Decomp f) where
  Decomp fs ==# Decomp fs' = fmap Lift1 fs == fmap Lift1 fs'
  
instance (Eq1 f, Eq a) => Eq (Decomp f a) where
  (==) = (==#)
  
instance Show1 f => Show1 (Decomp f) where
  showsPrec1 d (Decomp fs) =
    showsUnaryWith showsPrec "Decomp" d (fmap Lift1 fs)
  
instance (Show1 f, Show a) => Show (Decomp f a) where
  showsPrec = showsPrec1

  
type Decomps k = Compose (Comps k) (Node k)
  
letpath :: a -> Patt f (Maybe a)
letpath a = Just a :< Decomp []
  
instance S.Self a => S.Self (Patt f (Maybe a)) where
  self_ n = letpath (S.self_ n)
  
instance S.Local a => S.Local (Patt f (Maybe a)) where
  local_ n = letpath (S.local_ n)
  
instance S.Field a => S.Field (Patt f (Maybe a)) where
  type Compound (Patt f (Maybe a)) = S.Compound a
  p #. n = letpath (p S.#. n)

instance (S.Self k, Ord k, S.VarPath a)
  => S.Tuple (Patt (Decomps k) (Maybe a)) where
  type Tup (Patt (Decomps k) (Maybe a)) =
    Tup k (Patt (Decomps k) (Maybe a))
    
  tup_ ts = Nothing :< S.tup_ ts
  
instance (S.Self k, Ord k, S.VarPath a)
  => S.Tuple (Decomp (Decomps k) a) where
  type Tup (Decomp (Decomps k) a) = Tup k a
  tup_ ts = Decomp [c] where
    c = Compose (foldMap (Comps . getTup) ts)
  
instance S.Extend (Patt f a) where
  type Ext (Patt f a) = Decomp f (Patt f a)
  (a :< Decomp ns) # Decomp ns' = a :< Decomp (ns' ++ ns)
  