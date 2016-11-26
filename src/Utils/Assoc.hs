{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
module Utils.Assoc
  ( Assoc
  , assocLookup
  , assocInsert
  , assocDelete
  , assocConcat
  , assocLens
  , showAssoc
  ) where
import Control.Monad.Except
 ( MonadError
 , throwError
 )
import Control.Monad
 ( liftM2
 )
 
import qualified Error as E
import Utils.Lens
 ( Lens'
 , lens
 )

type Assoc k v = [(k, v)]

showAssoc :: Show k => Assoc k v -> String
showAssoc = show . fmap fst 

assocLookup :: (Show k, Ord k, MonadError E.Error m) => k -> Assoc k v -> m v
assocLookup key xs = maybe (throwError . E.UnboundVar $ showAssoc xs ++ "->" ++ show key) return (lookup key xs)

assocInsert :: (Show k, Ord k, MonadError E.Error m) => k -> v -> Assoc k v -> m (Assoc k v)
assocInsert key value e = return ((key, value):e)

assocDelete :: (Show k, Ord k, MonadError E.Error m) => k -> Assoc k v -> m (Assoc k v)
assocDelete key = return . filter ((key ==) . fst)

assocConcat :: (Show k, Ord k, MonadError E.Error m) => Assoc k v -> Assoc k v -> m (Assoc k v)
assocConcat x y = return (x ++ y)

assocLens :: (Show k, Ord k, MonadError E.Error m) => k -> Lens' (m (Assoc k v)) (m v)
assocLens key = lens (>>= assocLookup key) (\mxs ma -> do{ xs <- mxs; a <- ma; assocInsert key a xs})
