module Types.Eval.Cell
  ( newCell
  , viewCell
  , viewCellAt
  )
  where
  
import qualified Types.Error as E

import Control.Monad( join )
import Control.Monad.IO.Class
import Control.Monad.Catch( MonadThrow )
import Data.IORef
import Data.Typeable
import Data.Map as M


-- Cell
newCell :: MonadIO m => v -> m (IORef v)
newCell =
  liftIO . newIORef

  
viewCell :: MonadIO m => IORef (m v) -> m v
viewCell ref =
  do
    v <- join (liftIO (readIORef ref))
    liftIO (writeIORef ref (return v))
    return v
    

viewCellAt :: (MonadIO m, MonadThrow m, Ord k, Show k, Typeable k) => k -> M.Map k (IORef (m v)) -> m v
viewCellAt k x =
  maybe (E.throwUnboundVar k) viewCell (M.lookup k x)