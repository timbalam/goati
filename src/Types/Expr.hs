{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving, ScopedTypeVariables #-}
module Types.Expr
  ( Expr(..), fromList
  , Id(..)
  , Node(..)
  , E(..), toE
  , STree, pathSTree, punSTree, blockSTree
  , Vid, Tid, Member
  , ExprErrors
  , Label, Tag(..), Path, Vis(..), getvis
  , module Types.Primop
  )
  where
  

import Types.Parser( Label, Symbol(..), Tag(..), Path, Vis(..), getvis )
import qualified Types.Parser as Parser
import Types.Primop
import Types.Error

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap, (>=>) )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Functor.Identity
import Data.Monoid ( (<>) )
import Data.Bifunctor
import Data.Functor.Classes
import Data.List.NonEmpty( NonEmpty )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope( transverseScope, abstractEither )


-- Interpreted my-language expression
data Expr k a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block [Node (E k (Expr k) a)] (M.Map (Tag k) (Node (E k (Expr k) a)))
  | Expr k a `At` Tag k
  | Expr k a `Fix` M.Map (Tag k) (Node ())
  | Expr k a `Update` Expr k a
  | Prim (P (Expr k a))
  deriving (Eq, Functor, Foldable, Traversable)
  
  
fromList :: [Node (E k (Expr k) a)] -> [(Tag k, Node (E k (Expr k) a))] -> Expr k a
fromList es = Block es . M.fromList
  
  
newtype E k m a = E { unE :: Scope Int (Scope (Tag k) m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toE :: Monad m => m (Var (Tag k) (Var Int a)) -> E k m a
toE = E . toScope . toScope

 
newtype Id = SymbolId Integer | UnopId Parser.Unop | BinopId Parser.Binop
  deriving (Eq, Ord, Show)
  

  
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
    ((M.map . fmap) (>>>= f) se)
  e `At` x      >>= f = (e >>= f) `At` x
  e `Fix` m     >>= f = (e >>= f) `Fix` m
  e `Update` w  >>= f = (e >>= f) `Update` (w >>= f)
  Prim p        >>= f = Prim ((>>= f) <$> p)

  
instance Eq1 (Expr k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   = 
    (liftEq . liftEq) (liftEq eq) ena enb &&
    (liftEq . liftEq) (liftEq eq) sea seb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` ma)     (eb `Fix` mb)     =
    liftEq eq ea eb && ma == mb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (Prim pa)         (Prim pb)         =
    liftEq (liftEq eq) pa pb
  liftEq _  _                   _               = False
   
   
instance Show a => Show (Expr k a) where
  showsPrec = showsPrec1
   
   
instance Show1 (Expr k) where
  liftShowsPrec = go where 
    
    go :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr a -> ShowS
    go f g i e = case e of
      String s        -> showsUnaryWith showsPrec "String" i s
      Number d        -> showsUnaryWith showsPrec "Number" i d
      Bool b          -> showsUnaryWith showsPrec "Bool" i b
      Var a           -> showsUnaryWith f "Var" i a
      Block en se     -> showsBinaryWith f''' f'''' "fromList" i en (M.toList se)
      e `At` x        -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` m       -> showsBinaryWith f' showsPrec "Fix" i e m
      e `Update` w    -> showsBinaryWith f' f' "Update" i e w
      Prim p          -> showsUnaryWith f'' "Prim" i p
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
    
  

-- type aliases  
type Vid = Vis Id
type Tid = Tag Id
type ExprErrors k = NonEmpty (ExprError k)
type Member = Scope (Tag Id) Expr
  
  
-- Block internal tree structure
data Node k a = Closed a | Open (M.Map (Tag k) (Node a))
  deriving (Eq, Functor, Foldable, Traversable)

emptyNode = Open M.empty


mergeNode :: Node k a -> Node k a -> Collect (PathError k (Tag k)) (Node k a)
mergeNode (Open m)  (Open n)  = Open <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
mergeNode _         _         = (Collect . Left) (PathError M.empty)


instance Eq k => Eq1 (Node k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open ma)  (Open mb)  = liftEq (liftEq eq) ma mb
  liftEq _  _          _          = False

  
instance (Show k, Show a) => Show (Node k a) where
  showsPrec = showsPrec1
  
  
instance Show k => Show1 (Node k) where
  liftShowsPrec f g i e = case e of
    Closed a -> f i a
    Open m -> liftShowsPrec f' g' i m where
      f' = liftShowsPrec f g
      g' = liftShowList f g
  

instance Monoid (Collect (ExprErrors k) (Node k a)) where
  mempty = pure emptyNode
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeNode a b))


-- Set expression tree
data Ref a = Ref RefType a 

data RefType = Current | Lifted

newtype Build k a = B (S.Set k) (M.Map (Vis k) (Node k (Ref (Expr k a))))

emptyBuild = B S.empty M.empty


mergeBuild :: Ord k => Build k a -> Build k a -> Collect (PathError k (Vis k)) (Build k a)
mergeBuild (B sa ma) (B sb mb) = B <$> (sa <> sb) <*> unionAWith f ma mb where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
  
  
instance Ord k => Monoid (Collect (ExprErrors k) (Build k a)) where
  mempty = pure emptyBuild
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeBuild a b))
    
    
symBuild :: a -> Build a b
symbuild a = B (S.Singleton a) M.empty

    
pathBuild :: Path a (Vis a) -> Expr a b -> Build a b
pathBuild path = tree path . Ref Current


punBuild :: Path a (Vis a) -> Build a (Vis a)
punBuild path = tree (public <$> path) (refexpr path) where
  public = either (Pub . Label) Pub . getvis

  refexpr :: Path a (Vis a) -> Ref (Expr a (Vis a))
  refexpr (Pure k) = either
    (Ref Lifted . Var . Priv)
    (Ref Current . Var . Pub)
    (getvis k)
  refexpr (Free (path `Parser.At` x)) = Ref t (e `At` x) where
    Ref t e = refexpr path


tree :: Path a (Vis a) -> Ref (Expr a b) -> Build a b
tree p = go p . Closed
  where
    go (Pure a)                     = B S.empty . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
      
      
blockBuild :: Build a (Expr a (Vis a)) -> Expr a (Vis a)
blockBuild (B s m) =
  Block (M.elems en) se
  where
    (se, en) = M.foldrWithKey
      (\ k a (s, e) -> let a' = abstRef <$> a in case k of
        Priv x -> (s, M.insert x a' e)
        Pub x  -> (M.insert x a' s, e))
      (M.empty, M.empty)
      m
        
    abstRef :: Ref (Expr a (Vis a)) -> E a (Expr a) (Vis a)
    abstRef (Ref Current e) =
      (E . fmap Priv . abstract fenv) (abstractEither fself e)
    abstRef (Ref Lifted e) = lift e
    
    fself :: Vis a -> Either (Tag a) Label
    fself = \ e -> case e of
      Pub x                     -> Left x
      Priv l
        | M.member (Label l) se -> Left (Label l)
        | otherwise             -> Right l
      
    fenv :: Label -> Maybe Int
    fenv = flip M.lookupIndex en
    
  
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
