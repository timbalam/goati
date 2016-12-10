module Utils.Assoc
  ( Assoc
  , empty
  , lookup
  , insert
  , delete
  , concat
  ) where

type Assoc k v = k -> v -> Maybe v

empty :: Assoc k v
empty k v = Nothing

lookup :: Ord k => k -> v -> Assoc k v -> Maybe v
lookup k v f = f k v 

insert :: Ord k => (v -> Maybe k) -> (v -> Maybe v) -> Assoc k v -> Assoc k v
insert kf vf f k v =
  case
    kf v
  of
    Just a | a == k -> vf v
    Just a          -> f a v
    Nothing         -> Nothing

member :: Ord k => k -> v -> Assoc k v -> Bool
member k v = isJust . lookup k v

delete :: (Show k, Ord k) => k ->  Assoc k v -> Assoc k v
delete oldk f k v
  | k == oldk = Nothing
  | otherwise = f k v

concat :: (Ord k) => Assoc k v -> Assoc k v -> Assoc k v
concat f g k v = f k v <|> g k v
  
