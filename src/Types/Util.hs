module Types.Util
  where
  
import Control.Monad.Fix
import Control.Monad.Reader
import Data.Functor.Identity


-- EndoM
newtype EndoM m a = EndoM { appEndoM :: a -> m a }


instance Monad m => Monoid (EndoM m a) where
  mempty =
    EndoM return
  EndoM f `mappend` EndoM g =
    EndoM (f <=< g)

    
type Endo = EndoM Identity


endo :: Monad m => (a -> a) -> EndoM m a
endo f =
  EndoM (return . f)


appEndo :: Endo a -> (a -> a)
appEndo (EndoM f) =
  runIdentity . f


type Configurable m self super = EndoM (ReaderT self m) super


initial :: Monad m => a -> EndoM m a
initial a =
  EndoM (const (return a))


configure :: MonadFix m => (super -> m self) -> Configurable m self super -> m self
configure f (EndoM g) =
  mfix (runReaderT (mfix g >>= lift . f))


mapEndoM :: (m a -> n a) -> EndoM m a -> EndoM n a
mapEndoM f (EndoM g) =
  EndoM (f . g)