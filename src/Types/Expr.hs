{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables #-}
module Types.Expr
  ( Expr(..), blockList, fieldList
  , Key(..), Var(..)
  , Open(..), Node
  , Free(..)
  , E(..), toE
  , public, tag, var
  , Build, buildSym, buildPath, buildPun, blockBuild
  , BuildO(..), BuildN, buildNPath, matchBuild
  , Member, Ex, ExprErrors, Label
  , module Types.Prim
  )
  where
  

import Types.Parser( Label )
import qualified Types.Parser as Parser
import Types.Prim
import Util(  Collect(..), collect )

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap, (>=>) )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Functor.Identity
--import Data.Monoid ( (<>) )
import Data.Semigroup
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Classes
import Data.List.NonEmpty( NonEmpty, nonEmpty )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( abstractEither, bitransverseScope )

    
-- useful alias
type Member k = Scope k (Expr k)
type Ex k = Expr (Key k) (Vis (Key k))

-- Interpreted my-language expression
data Expr k a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block
      [Node k (E k (Expr k) a)]
      (Open k (Node k (E k (Expr k) a)))
  | Expr k a `At` k
  | Expr k a `Fix` k
  | Expr k a `Update` Expr k a
  | Expr k a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
newtype Open k a = Open { getOpen :: [(k, a)] }
  deriving (Eq, Functor, Foldable, Traversable)
  
  
type Node k = Free (Open k)


bitransverseFree
  :: Applicative f
  => (forall a a'. (a -> f a') -> t a -> f (u a'))
  -> (c -> f c')
  -> Free t c
  -> f (Free u c')
bitransverseFree _ f (Pure a) = Pure <$> f a
bitransverseFree tau f (Free ta) = Free <$> tau (bitransverseFree tau f) ta
  -- bitransverseFree tau f :: Free t c -> f (Free u c')
  -- tau (bitransverseFree tau f) :: t (Free t c) -> f (u (Free u c'))
  


fieldList :: [(k, Node k a)] -> Node k a
fieldList = Free . Open

  
blockList :: [Node k (E k (Expr k) a)] -> [(k, Node k (E k (Expr k) a))] -> Expr k a
blockList es = Block es . Open
  
  
newtype E k m a = E { unE :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toE :: Monad m => m (Var k (Var Int a)) -> E k m a
toE = E . toScope . toScope


bitraverseE
  :: (Bitraversable t, Applicative f)
  => (k -> f k')
  -> (a -> f a')
  -> E k (t k) a
  -> f (E k' (t k') a')
bitraverseE f g (E s) = E <$> bitransverseScope (bitransverseBound (bitraverse f) f) g s
-- bitraverse f :: ( a -> f a' ) -> t k a -> f (t k' a')
-- bitransverseScope (bitraverse f) :: ( c -> f c') -> Scope b (t k) c -> f (Scope b (t k') c')
-- bitransverseScope (bitransverseScope (bitraverse f)) :: ( d -> f d' ) -> Scope b1 (Scope b (t k)) d -> f (Scope b1 (Scope b (t k')) d')
  

bitransverseBound
  :: Applicative f
  => (forall a a'. (a -> f a') -> t a -> f (u a'))
  -> (b -> f b')
  -> (c -> f c')
  -> Scope b t c
  -> f (Scope b' u c')
bitransverseBound tau f g (Scope e) = Scope <$> tau (bitraverse f (tau g)) e

  
-- | Expr instances
instance Applicative (Expr k) where
  pure = return
  
  (<*>) = ap
  
instance Monad (Expr k) where
  return = Var
  
  String s      >>= _ = String s
  Number d      >>= _ = Number d
  Bool b        >>= _ = Bool b
  Var a         >>= f = f a
  Block en se   >>= f = Block
    ((map . fmap) (>>>= f) en)
    ((fmap . fmap) (>>>= f) se)
  e `At` x      >>= f = (e >>= f) `At` x
  e `Fix` m     >>= f = (e >>= f) `Fix` m
  e `Update` w  >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x  >>= f = (e >>= f) `AtPrim` x
    

instance Bifunctor Expr where
  bimap = bimapDefault
  
  
instance Bifoldable Expr where
  bifoldMap = bifoldMapDefault


instance Bitraversable Expr where
  bitraverse f g = go where
    
    go (Number d) = pure (Number d)
    go (String s) = pure (String s)
    go (Bool b) = pure (Bool b)
    go (Var a) = Var <$> g a
    go (Block es se) = liftA2 Block
      (traverse goFE es)
      (bitraverse f goFE se)
    go (e `At` k) = liftA2 At (go e) (f k)
    go (e `Fix` k) = liftA2 Fix (go e) (f k)
    go (e `Update` w) = liftA2 Update (go e) (go w)
    go (e `AtPrim` x) = (`AtPrim` x) <$> go e
  
    bitraverseF f = bitransverseFree (bitraverse f)
    goFE = bitraverseF f goE
    goE = bitraverseE f g

  
instance (Eq k, Eq a) => Eq (Expr k a) where
  (==) = eq1
  
  
instance Eq k => Eq1 (Expr k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   = 
    (liftEq . liftEq) (liftEq eq) ena enb &&
    (liftEq . liftEq) (liftEq eq) sea seb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (ea `AtPrim` xa)  (eb `AtPrim` xb)         =
    liftEq eq ea eb && xa == xb
  liftEq _  _                   _               = False
   
   
instance (Show k, Show a) => Show (Expr k a) where
  showsPrec = showsPrec1
   
   
instance Show k => Show1 (Expr k) where
  liftShowsPrec = go where 
    
    go :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr k a -> ShowS
    go f g i e = case e of
      String s        -> showsUnaryWith showsPrec "String" i s
      Number d        -> showsUnaryWith showsPrec "Number" i d
      Bool b          -> showsUnaryWith showsPrec "Bool" i b
      Var a           -> showsUnaryWith f "Var" i a
      Block en se     -> showsBinaryWith f''' f'''' "blockList" i en (getOpen se)
      e `At` x        -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` x       -> showsBinaryWith f' showsPrec "Fix" i e x
      e `Update` w    -> showsBinaryWith f' f' "Update" i e w
      e `AtPrim` p    -> showsBinaryWith f' showsPrec "AtPrim" i e p
      where
        f'''' = liftShowsPrec f''' g'''
      
        f''' :: (Show1 f, Show1 g, Show1 h) => Int -> f (g (h a)) -> ShowS
        f''' = liftShowsPrec f'' g''
        
        g''' :: (Show1 f, Show1 g, Show1 h) => [f (g (h a))] -> ShowS
        g''' = liftShowList f'' g''
        
        f'' :: (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
        f'' = liftShowsPrec f' g'
        
        g'' :: (Show1 f, Show1 g) => [f (g a)] -> ShowS
        g'' = liftShowList f' g'
        
        f' :: Show1 f => Int -> f a -> ShowS
        f' = liftShowsPrec f g
        
        g' :: Show1 f => [f a] -> ShowS
        g' = liftShowList f g
        

        
-- | Open instances
instance Bifunctor Open where
  bimap f g (Open xs) = Open (bimap f g <$> xs)
  
  
instance Bifoldable Open where
  bifoldMap f g (Open xs) = foldMap (bifoldMap f g) xs
  
  
instance Bitraversable Open where
  bitraverse f g (Open xs) = Open <$> traverse (bitraverse f g) xs

  
instance Eq k => Eq1 (Open k) where
  liftEq eq (Open fa) (Open fb) = liftEq (liftEq eq) fa fb
  
  
instance Eq k => Eq1 (Free (Open k)) where
  liftEq eq (Pure a)  (Pure b)  = eq a b
  liftEq eq (Free fa) (Free fb) = liftEq (liftEq eq) fa fb
  liftEq _  _         _         = False


instance Show k => Show1 (Free (Open k)) where
  liftShowsPrec f g i (Pure a) =
    showsUnaryWith f "Pure" i a
    
  liftShowsPrec f g i (Free (Open xs)) =
    showsUnaryWith (const g'') "fieldList" i xs where
      -- [f (g a)] -> ShowS
      g'' = liftShowList f' g'
      
      -- Int -> f a -> ShowS
      f' = liftShowsPrec f g
      -- [f a] -> ShowS
      g' = liftShowList f g
      
  
-- | E instances
instance MonadTrans (E k) where
  lift = E . lift . lift
  
  
instance Bound (E k)
  
  
instance (Monad m, Show1 m, Show a, Show k) => Show (E k m a) where
  showsPrec = showsPrec1
    
    
instance (Monad m, Show1 m, Show k) => Show1 (E k m) where
  liftShowsPrec f g i m =
    (showsUnaryWith f''' "toE" i . fromScope . fromScope) (unE m) where
    f''' = liftShowsPrec  f'' g''
      
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    f'' = liftShowsPrec f' g'
    g'' = liftShowList f' g'
    
    

-- | Expression key type
data Key k =
    Label Label
  | Symbol k
  | Id Int
  | Self
  | Unop Parser.Unop
  | Binop Parser.Binop
  deriving (Eq, Ord, Show)
      
    
tag :: Parser.Tag -> Key Parser.Symbol
tag (Parser.Label l) = Label l
tag (Parser.Symbol s) = Symbol s
  
  
-- | Expression variable type
data Vis a =
    Priv Label
  | Pub a
  deriving (Eq, Ord, Show)
  
  
var :: Parser.Var -> Vis (Key Parser.Symbol)
var (Parser.Pub t) = Pub (tag t)
var (Parser.Priv l) = Priv l
  
  
-- Block field tree builder
data Build a = Build
  { symbols :: S.Set Parser.Symbol
  , fields :: M.Map Parser.Var (BuildN (Ref a))
  }
  
data Ref a = R RefType a 

data RefType = Current | Lifted

newtype BuildO a = BuildO (M.Map Parser.Tag a)
  deriving (Eq, Functor, Foldable, Traversable)
  
type BuildN = Free BuildO

  
emptyBuild = Build S.empty M.empty
    
emptyBuildN = Free (BuildO M.empty)
      
  
-- | Errors when building block field tree
data ExprError =
    OlappedMatch Paths
  | OlappedSet Parser.Var Paths
  | OlappedSym Parser.Symbol
  deriving (Eq, Show)
  
type ExprErrors = NonEmpty ExprError

data Paths = Paths (M.Map Parser.Tag Paths) deriving (Eq, Show)
  
  
instance Semigroup Paths where
  Paths a <> Paths b = Paths (M.unionWith (<>) a b)
  
listPaths :: Paths -> [Parser.Path Parser.Tag]
listPaths (Paths m) = M.foldMapWithKey (go . Pure) m where
  go :: Parser.Path a -> Paths -> [Parser.Path a]
  go p (Paths m) = if M.null m then [p] else 
    M.foldMapWithKey (go . Free . Parser.At p) m
    

mergeBuild :: Build a -> Build a -> Collect ExprErrors (Build a)
mergeBuild (Build sa ma) (Build sb mb) =
  liftA2 Build (mergeSyms sa sb) (unionAWith fnode ma mb)
  where
    fnode k a b = first
      (pure . OlappedSet k)
      (mergeBuildF a b)
    
    mergeSyms sa sb = case nonEmpty (S.toList (S.intersection sa sb)) of
      Nothing -> pure (S.union sa sb)
      Just xs -> collect (OlappedSym <$> xs)


mergeBuildF :: BuildN a -> BuildN a -> Collect Paths (BuildN a)
mergeBuildF (Free (BuildO m)) (Free (BuildO n)) =
  Free . BuildO <$> unionAWith f m n where
    f k a b = first (Paths . M.singleton k) (mergeBuildF a b)
    
mergeBuildF _ _ =
  collect (Paths M.empty)
  

instance Monoid (Collect ExprErrors (Build a)) where
  mempty = pure emptyBuild
  
  a `mappend` b = either
    collect
    id
    (getCollect (liftA2 mergeBuild a b))
    
    
instance Monoid (Collect ExprErrors (BuildN a)) where
  mempty = pure emptyBuildN
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeBuildF a b))
    
    
-- | nested match tree builder
buildNPath :: Parser.Path Parser.Tag -> a -> BuildN a
buildNPath path = go path . Pure
  where
    go (Pure x)                     = Free . BuildO . M.singleton x
    go (Free (path `Parser.At` x))  = go path . Free . BuildO . M.singleton x
        
        
matchBuild
  :: Monoid m
  => (Expr (Key Parser.Symbol) a -> m)
  -> BuildN (Expr (Key Parser.Symbol) a -> m)
  -> Expr (Key Parser.Symbol) a
  -> m
matchBuild _ (Pure f) e = f e
matchBuild k b@(Free (BuildO m)) e = k (foldr (flip Fix . tag) e (M.keys m))
  `mappend` go b e where
    go
      :: Monoid m
      => BuildN (Expr (Key Parser.Symbol) a -> m)
      -> Expr (Key Parser.Symbol) a
      -> m
    go (Pure f) e = f e
    go (Free (BuildO m)) e = M.foldMapWithKey
      (flip go . At e . tag)
      m
  
    
-- | block field tree builder
buildSym :: Parser.Symbol -> Build a
buildSym s = Build (S.singleton s) M.empty
    
    
buildPath :: Parser.Path Parser.Var -> a -> Build a
buildPath path = tree path . R Current


buildPun
  :: Parser.Path Parser.Var
  -> Build (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
buildPun path = tree (public <$> path) (refexpr path) where
  refexpr :: Parser.Path Parser.Var -> Ref (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
  refexpr (Pure (Parser.Pub x)) = (R Current . Var . Pub) (tag x)
  refexpr (Pure (Parser.Priv l)) = (R Lifted . Var) (Priv l)
  refexpr (Free (path `Parser.At` x)) = R t (e `At` tag x) where
    R t e = refexpr path
    
    
public :: Parser.Var -> Parser.Var
public x@(Parser.Pub _) = x
public (Parser.Priv l) = Parser.Pub (Parser.Label l)


tree :: Parser.Path Parser.Var -> Ref a -> Build a
tree p = go p . Pure
  where
    go (Pure a)                     = Build S.empty . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Free . BuildO . M.singleton x

      
      
blockBuild
  :: Int
  -> Build (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
  -> (Int, Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
blockBuild count (Build syms m) =
  (count + S.size syms, blockList (M.elems en) pub)
  where
    (priv, pub) = (partitionVis . M.toAscList) (M.map (hoistFree buildO . fmap abstRef) m)
    se = M.fromAscList pub
    en = M.fromAscList priv
      
    partitionVis = foldr
      (\ (k, a) (priv, pub) -> case k of
        Parser.Priv l -> ((l, a):priv, pub)
        Parser.Pub t -> (priv, (tag t, a):pub))
      ([], [])
      
    buildO :: BuildO a -> Open (Key Parser.Symbol) a
    buildO (BuildO m) = (Open . map (first tag)) (M.toAscList m)
        
    abstRef :: Ref (Expr (Key k) (Vis (Key k))) -> E (Key k) (Expr (Key k)) (Vis (Key k))
    abstRef (R Current e) =
      (E . fmap Priv . abstract fenv) (abstractEither fself e)
    abstRef (R Lifted e) = lift e
    
    fself :: Vis (Key k) -> Either (Key k) Label
    fself = \ e -> case e of
      Pub k                     -> Left k
      Priv l
        | M.member (Label l) se -> Left (Label l)
        | otherwise             -> Right l
      
    fenv :: Label -> Maybe Int
    fenv = flip M.lookupIndex en
    
    fsym :: Parser.Symbol -> Key Parser.Symbol
    fsym k = case S.lookupIndex k syms of
      Nothing -> Symbol k
      Just i -> Id (i + count)
  
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
