{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module My.Types.Paths.Patt
  ( module My.Types.Paths.Patt
  , module My.Types.Paths.Tup
  )
  where
  
  
import qualified My.Types.Syntax.Class as S
import My.Types.Paths.Tup
import Control.Comonad.Cofree

      
-- | Pattern
type Patt f = Cofree (Decomp f)
newtype Decomp f a = Decomp { getDecomp :: [f a] }
  deriving (Functor, Foldable, Traversable)
  
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
  => S.Tuple (Patt (Comps k) (Maybe a)) where
  type Tup (Patt (Comps k) (Maybe a)) =
    Tup k (Patt (Comps k) (Maybe a))
    
  tup_ ts = Nothing :< S.tup_ ts
  
instance (S.Self k, Ord k, S.VarPath a)
  => S.Tuple (Decomp (Comps k) a) where
  type Tup (Decomp (Comps k) a) = Tup k a
  tup_ ts = Decomp [foldMap (Comps . getTup) ts]
  
instance S.Extend (Patt (Comps k) a) where
  type Ext (Patt (Comps k) a) =
    Decomp (Comps k) (Patt (Comps k) a)
  (a :< Decomp ns) # Decomp ns' = a :< Decomp (ns' ++ ns)
  