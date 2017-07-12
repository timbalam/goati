{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Types.Eval.Ided
  ( Ided
  , Id
  , Ids
  , useId
  , runIded
  )
  where
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.Reader

newtype Id = Id Word deriving (Eq, Ord)
instance Show Id where show (Id i) = show i
type Ids = [Id]
newtype Ided m a = Ided (StateT Ids m a) deriving (Functor, Applicative, Monad, MonadState Ids, MonadIO, MonadTrans, MonadError e, MonadWriter w, MonadReader r, MonadFix)

useId :: MonadState Ids m => (Id -> a) -> m a
useId ctr = state (\ (x:xs) -> (ctr x, xs))

runIded :: Monad m => Ided m a -> m a    
runIded (Ided m) = evalStateT m (Id `fmap` iterate succ 0)

