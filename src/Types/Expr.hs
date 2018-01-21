{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveAnyClass, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, ScopedTypeVariables #-}
module Types.Expr
  ( Expr(..), fromList
  , Id(..)
  , Node(..)
  , E(..), toE
  , Build, pathBuild, punBuild, build
  , Member, ExprErrors, Label
  , module Types.Primop
  )
  where
  

import Types.Parser( Label )
import qualified Types.Parser as Parser
import Types.Primop
import Util(  Collect(..), collect )

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap, (>=>) )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Functor.Identity
--import Data.Monoid ( (<>) )
import Data.Semigroup
import Data.Bifunctor
import Data.Bifunctor.Tannen
import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Classes
import Data.List.NonEmpty( NonEmpty, nonEmpty )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( transverseScope, abstractEither, mapBound )


-- Interpreted my-language expression
data Expr k a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block
      [F k (E k (Expr k) a)]
      [(k , F k (E k (Expr k) a))]
  | Expr k a `At` k
  | Expr k a `Fix` [(k, F k ())]
  | Expr k a `Update` Expr k a
  | Expr k a `AtPrim` ()
  deriving (Eq, Functor, Foldable, Traversable)
  
  
newtype Open k a = Open { getOpen :: [(k, a)] }
  deriving (Eq, Eq1, Functor, Foldable, Traversable)
  
type F k = Free (Open k)
  
  
fromList
  :: [F k (E k (Expr k) a)]
  -> [(k, F k (E k (Expr k) a))]
  -> Expr k a
fromList es = Block es . Open


mapExprKeys :: (k -> k') -> Expr k a -> Expr k' a
mapExprKeys f = go where
  go (Number d) = Number d
  go (String s) = String s
  go (Bool b) = Bool b
  go (Var a) = Var a
  go (Block es se) = Block
    (map mapFE es)
    (bimap f mapFE se)
  go (e `At` k) = go e `At` f k
  go (e `Fix` m) = bimap f mapF m
  go (e `Update` w) = go e `Update` go w
  go (e `AtPrim` x) = go e `AtPrim` x
  
  mapFE = mapF . fmap mapE
  mapE = mapEBound f . hoistE go
  mapF f = hoistFree (first f)
  
  
newtype E k m a = E { unE :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toE :: Monad m => m (Var (Key k) (Var Int a)) -> E k m a
toE = E . toScope . toScope


hoistE :: Functor f => (forall x. f x -> g x) -> E k f a -> E k g a
hoistE f = E . hoistScope (hoistScope f) . unE


mapEBound :: Ord k' => (k -> k') -> E k m a -> E k' m a
mapEBound f = E . hoistScope (mapBound f) . unE

  
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
    ((fmap . fmap . fmap) (>>>= f) se)
  e `At` x      >>= f = (e >>= f) `At` x
  e `Fix` m     >>= f = (e >>= f) `Fix` m
  e `Update` w  >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x  >>= f = (e >>= f) `AtPrim` x

  
instance Eq k => Eq1 (Expr k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   = 
    (liftEq . liftEq) (liftEq eq) ena enb &&
    (liftEq . liftEq . liftEq) (liftEq eq) sea seb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` ma)     (eb `Fix` mb)     =
    liftEq eq ea eb && ma == mb
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
      Block en se     -> showsBinaryWith f''' f'''' "fromList" i en se
      e `At` x        -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` m       -> showsBinaryWith f' showsPrec "Fix" i e m
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
  | Unop Parser.Unop
  | Binop Parser.Binop
  deriving (Eq, Ord, Show)
  
  
-- | Expression variable type
data Vis a =
    Priv Label
  | Pub a
  deriving (Eq, Ord, Show)
    
  

-- type aliases
type Member k = Scope k (Expr k)
  
  
-- Block field tree builder
data Build a = Build
  { symbols :: S.Set Parser.Symbol
  , fields :: M.Map Parser.Var (BuildF (Ref a))
  }
  
data Ref a = R RefType a 

data RefType = Current | Lifted

newtype BuildO a = BuildO (M.Map Parser.Tag a)
  deriving (Eq, Functor, Foldable, Traversable)
  
type BuildF = Free BuildO
  
  
emptyBuild = Build S.empty M.empty
    
emptyBuildF = Free (BuildO M.empty)
      
  
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


mergeBuildF :: BuildF a -> BuildF a -> Collect Paths (BuildF a)
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
    
    
instance Monoid (Collect ExprErrors (BuildF a)) where
  mempty = pure emptyBuildF
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeBuildF a b))
  
    
symBuild :: Parser.Symbol -> Build a
symBuild s = Build (S.singleton s) M.empty
    
    
pathBuild :: Parser.Path Parser.Var -> a -> Build a
pathBuild path = tree path . R Current


punBuild
  :: Parser.Path Parser.Var
  -> Build (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
punBuild path = tree (public <$> path) (refexpr path) where
  public (Parser.Pub x) = Parser.Pub x
  public (Parser.Priv l) = Parser.Pub (Parser.Label l)

  refexpr :: Parser.Path Parser.Var -> Ref (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
  refexpr (Pure (Parser.Pub x)) = (R Current . Var . Pub) (tag x)
  refexpr (Pure (Parser.Priv l)) = (R Lifted . Var) (Priv l)
  refexpr (Free (path `Parser.At` x)) = R t (e `At` tag x) where
    R t e = refexpr path


tree :: Parser.Path Parser.Var -> Ref a -> Build a
tree p = go p . Pure
  where
    go (Pure a)                     = Build S.empty . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Free . BuildO . M.singleton x
    
    
tag :: Parser.Tag -> Key Parser.Symbol
tag (Parser.Label l) = Label l
tag (Parser.Symbol s) = Symbol s
      
      
build
  :: Int
  -> Build (Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
  -> (Int, Expr (Key Parser.Symbol) (Vis (Key Parser.Symbol)))
build count (Build syms m) =
  (count + S.size syms, Block (M.elems en) pub)
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
    
