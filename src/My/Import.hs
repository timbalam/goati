module My.Import
  ( substpaths
  , sourcefile
  , programimports
  , exprimports
  , findimports
  , checkimports
  , SrcTree(..)
  )
where

import qualified My.Types.Parser as P
import My.Types.Interpreter (KeySource(..))
import qualified My.Types.Classes
import My.Parser (showMy, readsMy, parse)
import My.Util (Collect(..), collect)
import qualified System.Directory
import qualified System.FilePath
import System.FilePath ((</>), (<.>))
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Data.Typeable (Typeable)
import Data.Bifunctor (first)
import Data.Bitraversable (bitraverse)
import Data.Semigroup ((<>))
import Control.Applicative (liftA2)
import Control.Monad.Catch (MonadThrow(..))
import Control.Monad.IO.Class (MonadIO(..))


-- | Import path resolution machinery
data SrcTree =
  SrcTree FilePath (P.Program P.Import) (M.Map P.Import SrcTree)
  
  
data ImportError = ImportNotFound KeySource P.Import
  deriving (Eq, Show, Typeable)
  

instance My.Types.Classes.MyError ImportError where
  displayError (ImportNotFound src i) =
    "Not found: Module " ++ showMy i ++ "\nIn :" ++ show src
     
      
substpaths
  :: Traversable t
  => KeySource
  -> M.Map P.Import SrcTree
  -> t P.Import
  -> Either [ImportError] (M.Map FilePath (P.Program FilePath), t FilePath)
substpaths f m p = (getCollect . bitraverse
  (M.traverseWithKey (checkimports . File))
  (checkimports f))
  (go p m)
  where
    go
      :: Functor f
      => f P.Import
      -> M.Map P.Import SrcTree
      -> (M.Map FilePath (P.Program (Either FilePath P.Import)),
        f (Either FilePath P.Import))
    go p map = (flatimports map, subst <$> p)
      where
        subst :: P.Import -> Either FilePath P.Import
        subst i = maybe (Right i) (\ (SrcTree f _ _) -> Left f) (M.lookup i map)
    
        flatimports
          :: M.Map P.Import SrcTree -> M.Map FilePath (P.Program (Either FilePath P.Import))
        flatimports m = ((>>= subst) <$>) <$> (M.fromList (M.elems m') <> s) where
          (s, m') = traverse (\ (SrcTree f p m) -> (,) f <$> go p m) m
        
        
checkimports
  :: Traversable t
  => KeySource
  -> t (Either a P.Import)
  -> Collect [ImportError] (t a)
checkimports file p = first (ImportNotFound file <$>) (closed p)
  where
  closed :: Traversable t => t (Either a b) -> Collect [b] (t a)
  closed = traverse (\ k -> case k of
    Left f -> pure f
    Right i -> collect (pure i))
  

sourcefile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> m (M.Map P.Import (), SrcTree)
sourcefile file =
  liftIO (T.readFile file)
  >>= My.Types.Classes.throwLeftMy . parse readsMy file
  >>= \ p -> do 
    (s, m) <- findimports [dir] (programimports p)
    return (s, SrcTree file p m)
  where
    dir = System.FilePath.dropExtension file
  

programimports :: P.Program P.Import -> M.Map P.Import ()
programimports = foldMap (flip M.singleton mempty)

  
exprimports :: P.Expr (P.Res a P.Import) -> M.Map P.Import ()
exprimports = (foldMap . foldMap) (flip M.singleton mempty)
        
        
findimports
  :: (MonadIO m, MonadThrow m)
  => [FilePath]
  -> M.Map P.Import ()
  -> m (M.Map P.Import (), M.Map P.Import SrcTree)
findimports dirs s = loop s mempty mempty where

  loop x s m = do
    (xout, (sout, mout)) <- findset dirs mempty x mempty
    -- don't retry imports already tried in these directories
    let xout' = M.difference (M.difference xout s) m
    if M.null xout' then
      -- no new imports to resolve
      return (sout <> s, mout <> m)
    else
      -- try to resolve inherited imports on path
      loop xout (sout <> s) (mout <> m)
      
  findset [] x s m = return (x, (s, m))
  findset (dir:dirs) x s m = do 
    (xout, (sout, mout)) <- resolveimports dir s
    findset dirs (x <> xout) sout (m <> mout)
    
    
resolveimports
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> M.Map P.Import ()
  -> m (M.Map P.Import (), (M.Map P.Import (), M.Map P.Import SrcTree))
resolveimports dir = go where

  go s = do
    -- try to resolve imports in directory
    stry <- M.traverseWithKey (\ i () -> resolve dir i) s
    let 
      -- separate resolved imports
      (sout, spairs) = M.mapEither ((maybe . Left) () Right) stry
      
      -- combine inherited unresolved imports
      (nw, mout) = sequenceA spairs
      
    return (nw, (sout, mout))
      
  
resolve
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> P.Import
  -> m (Maybe (M.Map P.Import (), SrcTree))
resolve dir (P.Use (P.I_ l)) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    Just <$> sourcefile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
