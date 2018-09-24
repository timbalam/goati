{-# LANGUAGE RankNTypes, FlexibleInstances, FlexibleContexts, TypeFamilies, ScopedTypeVariables #-}
module My.Types.Paths.Rec
  ( module My.Types.Paths.Rec
  , module My.Types.Paths.Path
  )
  where
  
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import My.Types.Paths.Path
import My.Util ((<&>))
import Control.Monad.State
import Data.Coerce
import Data.List (nub)
import Data.Maybe (mapMaybe)

  
-- | Recursive block with destructing pattern assignments. 
newtype Rec w a = Rec (w, Maybe a)

decl :: s -> Rec [s] a
decl s = Rec ([s], Nothing)
  
  
instance S.Self s => S.Self (Rec [s] a) where
  self_ n = decl (S.self_ n)

instance S.Field s => S.Field (Rec [s] a) where
  type Compound (Rec [s] a) = S.Compound s
  p #. n = decl (p S.#. n)

instance (Traversable f, S.Patt (f (Maybe s)))
  => S.Let (Rec [s] (f Bind, a)) where
  type Lhs (Rec [s] (f Bind, a)) = f (Maybe s)
  type Rhs (Rec [s] (f Bind, a)) = a
  p #= a = Rec (traverse 
    (maybe (pure Skip) (\ s -> ([s], Bind)))
    p <&> (\ p' -> Just (p', a)))
    

-- | A leaf pattern that can bind the matched value or skip
data Bind = Bind | Skip

bind :: a -> a -> Bind -> a
bind a _ Bind = a
bind _ a Skip = a


buildVis
  :: forall k a. (S.Self k, Ord k)
  => [Rec [P.Vis (Path k) (Path k)] a]
  -> (Vis k (Node k (Maybe Int)), [a], [S.Ident])
buildVis rs = (visFromList kvs, pas, ns) where
  pas = mapMaybe (\ (Rec (_, pa)) -> pa) rs
  kvs = enumJust (coerce rs
    :: [([P.Vis (Path k) (Path k)], Maybe a)])
  ns = nub (foldMap (pure . name . fst) kvs)
  
  name :: P.Vis (Path k) (Path k) -> S.Ident
  name (P.Pub (Path n _)) = n
  name (P.Priv (Path n _)) = n
  
  enumJust :: forall a b . [([a], Maybe b)] -> [(a, Maybe Int)]
  enumJust cs = concat (evalState (traverse enumPair cs) 0) where
    
    enumPair (xs, Just _) = 
      traverse (\ a -> state (\ i -> ((a, Just i), i+1))) xs
    enumPair (xs, Nothing) = pure (map (flip (,) Nothing) xs)
