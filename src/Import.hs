module Import
  ( substpaths
  , sourcefile
  , programimports
  , exprimports
  , findimports
  )
where

import qualified Types.Parser as P
import Types.Parser( Import(..) )
import Util


--import System.IO( FilePath )
import qualified System.Directory
import qualified System.FilePath
import System.FilePath( (</>), (<.>) )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import Control.Monad.Catch
import Control.Monad.IO


-- | Import machinery
data SrcTree =
  SrcTree FilePath (P.Program Import) (M.Map Import SrcTree)
     
      
substpaths
  :: Traversable t
  => M.Map Import SrcTree
  -> t FilePath
  -> Either [ScopeError] (M.Map FilePath (P.Program FilePath), t FilePath)
substpaths m p = liftA2 (,) cs cp where
  (s, p) = go p m
  cs = M.traverseWithKey checkimports s
  cp = checkimports f p

  go
    :: Functor f
    => f FilePath
    -> M.Map Import SrcTree
    -> (M.Map FilePath (P.Program (Either FilePath Import)),
      f (Either FilePath Import))
  go p map = (flatimports map, (subst >>=) <$> p)
    where
      subst :: Import -> Either FilePath Import
      subst i = maybe (Right i) (\ (SrcTree f _ _) -> Left f) (M.lookup i map)
  
      flatimports
        :: M.Map Import SrcTree -> M.Map FilePath (P.Program (Either FilePath Import))
      flatimports m = ((subst >>=) <$>) <$> (M.fromList (M.elems m') <> s) where
        (s, m') = traverse (\ (SrcTree _ p m) -> go p m) m
        
        
checkimports
  :: Traversable t
  => FilePath
  -> t (Either FilePath Import)
  -> Collect [ScopeError] (t FilePath)
checkimports file p = first (ImportNotFound (File file)) (closed p)
  where
  closed :: Traversable t => t (Either a b) -> Collect [b] (t a)
  closed = traverse (\ k -> case k of
    Left f -> pure f
    Right i -> collect (pure i))
  

sourcefile
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> m (M.Map Import (), SrcTree)
sourcefile file dirs =
  liftIO (T.readFile file)
  >>= throwLeftMy . parse readsMy file
  >>= \ p -> do 
    (s, m) <- findimports [dir] (programimports p)
    return (s', SrcTree file p m)
  where
    dir = System.FilePath.dropExtension file
  

programimports :: P.Program Import -> M.Map Import ()
programimports = foldMap (flip M.singleton mempty)

  
exprimports :: P.Expr (Res a Import) -> M.Map Import ()
exprimports = (foldMap . foldMap) (flip M.singleton mempty)
        
        
findimports
  :: (MonadIO m, MonadThrow m)
  => [FilePath]
  -> M.Map Import ()
  -> m (M.Map Import (), M.Map Import SrcTree)
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
  -> M.Map Import ()
  -> m (M.Map Import (), (M.Map Import (), M.Map Import SrcTree))
resolveimports dir = go where

  go s = do
    -- try to resolve imports in directory
    stry <- M.traverseWithKey (\ i () -> resolve dir i) s
    let 
      -- separate resolved imports
      (sout, spairs) = mapEither ((maybe . Left) () Right) stry
      
      -- combine inherited unresolved imports
      (nw, mout) = sequenceA spairs
      
    return (nw, (sout, mout))
      
  
resolve
  :: (MonadIO m, MonadThrow m)
  => FilePath
  -> Import
  -> m (Maybe (M.Map Import (), SrcTree))
resolve dir (Use l) = do
  test <- liftIO (System.Directory.doesPathExist file)
  if test then
    sourcefile file
  else return Nothing
  where
    file = dir </> T.unpack l <.> "my"
