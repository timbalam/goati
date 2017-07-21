module Types.Eval.Scope
  ( Scope
  , Classed
  , toConfigurable
  , toClassed
  )
  where
  
import qualified Types.Error as E
import Types.Util

import Control.Monad.Writer
import Control.Monad.Reader


{-
n      -- constructed monad
-> a   -- constructed type
-> m   -- inner monad
-> b   -- inner type
-}

-- Scope n a m b ~ b -> (b, a) -> m (a -> n a, b)
type Scope n a m b = 
  Configurable (WriterT (EndoM n a) m) (b, a) b
  --EndoM (ReaderT (b, a) (WriterT (EndoM n a) m)) b


-- Classed m a ~ a -> (a -> m a)
type Classed m a =
  Configurable m a a
  --EndoM (ReaderT a m) a


toConfigurable :: Monad m => Scope n a m b -> Configurable (ReaderT a (WriterT (EndoM n a) m)) b b
toConfigurable =
  mapEndoM nestReaderT
    where
      nestReaderT :: ReaderT (a, b) m c -> ReaderT a (ReaderT b m) c
      nestReaderT m = ReaderT (flip withReaderT m . (,))  

      
toClassed :: Monad m => ReaderT a (WriterT (EndoM (ReaderT a m) a) m) b -> Classed m a
toClassed =
  commuteAndJoin . writeM
    where
      writeM :: Monad m => ReaderT a (WriterT w m) b -> ReaderT a m w
      writeM =
        mapReaderT execWriterT
    
      commuteAndJoin :: Monad m => m (EndoM m a) -> EndoM m a
      commuteAndJoin m =
        EndoM
          (\ b0 ->
             do
               EndoM f <- m
               f b0)

    