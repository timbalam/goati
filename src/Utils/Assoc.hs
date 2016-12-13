module Utils.Assoc
  ( Assoc
  , Assocs
  , looksup
  , inserts
  , members
  , deletes
  , concats
  ) where

type Assoc k v = [(k, v)]
type Assocs k v = Assoc k v -> Assoc k v

looksup :: Ord k => k -> (Assoc k v -> Assoc k v) -> Maybe v
looksup k v f = f [] `lookup` k

inserts :: Ord k => (Assoc k v -> k) -> v -> Assocs k v -> Assocs k v
inserts kf v f xs = xs++t++ts
  where
    t = [(kf (xs++ts), v)]
    ts = f (xs++t)
  

members :: Ord k => k -> Assocs k v -> Bool
members k f = k `elem` (fst `fmap` f [])

deletes :: (Ord k) => (Assoc k v -> k) -> Assocs k v -> Assocs k v
deletes kf f xs = filter ((/= k) . fst) (xs++ts)
  where
    k = kf (xs++ts)
    ts = f xs

concats :: (Ord k) => Assocs k v -> Assocs k v -> Assocs k v
concats f g xs = xs++ys++ts
  where
    ys = f (xs++ts)
    ts = g (xs++ys)
  
