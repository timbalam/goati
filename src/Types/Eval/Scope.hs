module Types.Eval.Scope
  where
import qualified Types.Error as E
import Types.Util

import Control.Monad.Writer
import Control.Monad.Reader


--  n      -- constructed monad
--  -> a   -- constructed type
--  -> m   -- inner monad
--  -> b   -- inner type
type EWriterT n a m = WriterT (EndoM n a) m
type Scope n a m b = EndoM (ReaderT (b, a) (EWriterT n a m)) b
type Classed m a = EndoM (ReaderT a m) a

toConfigurable :: Monad m => Scope n a m b -> Configurable (ReaderT a (EWriterT n a m)) b b
toConfigurable = mapEndoM nestReaderT
  where
    nestReaderT :: ReaderT (a, b) m c -> ReaderT a (ReaderT b m) c
    nestReaderT m = ReaderT (flip withReaderT m . (,))

toClassed :: Monad m => ReaderT a (EWriterT (ReaderT a m) a m) b -> Classed m a
toClassed = commuteAndJoin . writeM
  where
    writeM :: Monad m => ReaderT a (WriterT w m) b -> ReaderT a m w
    writeM = mapReaderT execWriterT
    
    commuteAndJoin :: Monad m => m (EndoM m a) -> EndoM m a
    commuteAndJoin m =
      EndoM (\ b0 -> do{ EndoM f <- m; f b0 })

    