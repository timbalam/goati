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
  

import Types.Parser( Label, Tag(..), Path, Vis(..), getvis )
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
data Expr a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block [Node (E Expr a)] (M.Map Tid (Node (E Expr a)))
  | Expr a `At` Tid
  | Expr a `Fix` M.Map Tid (Node ())
  | Expr a `Update` Expr a
  | Primop (Primop (Expr a))
  deriving (Eq, Functor, Foldable, Traversable)
  
  
fromList :: [Node (E Expr a)] -> [(Tid, Node (E Expr a))] -> Expr a
fromList es = Block es . M.fromList
  
  
newtype E m a = E { unE :: Scope Int (Scope Tid m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toE :: Monad m => m (Var Tid (Var Int a)) -> E m a
toE = E . toScope . toScope
  
 
data Id =
    BlockId Integer
  | StrId T.Text
  | FloatId Rational
  | IntId Integer
  deriving (Eq, Ord, Show)
  

-- type aliases  
type Vid = Vis Id
type Tid = Tag Id
type ExprErrors a = NonEmpty (ExprError Id a)
type Member = Scope Tid Expr

  
instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
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
  Primop op     >>= f = Primop ((>>= f) <$> op)

  
instance Eq1 Expr where
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
  liftEq eq (Primop opa)      (Primop opb)      =
    primEq opa opb
    where
      primEq (NumberBinop opa da a) (NumberBinop opb db b)  =
        opa == opb && da == db && liftEq eq a b
      primEq (BoolBinop opa ba a)   (BoolBinop opb bb b)    =
        opa == opb && ba == bb && liftEq eq a b
      primEq _                      _                       =
        False
  liftEq _  _                   _               = False
   
   
instance Show a => Show (Expr a) where
  showsPrec = showsPrec1
   
   
instance Show1 Expr where
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
      Primop op       -> showsPrimopWith f' i op
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
      
  
instance MonadTrans E where
  lift = E . lift . lift
  
  
instance Bound E
  
  
instance (Monad m, Show1 m, Show a) => Show (E m a) where
  showsPrec = showsPrec1
    
    
instance (Monad m, Show1 m) => Show1 (E m) where
  liftShowsPrec f g i m =
    (showsUnaryWith (liftShowsPrec f'' g'') "toE" i
      . fromScope . fromScope) (unE m) where
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    f'' = liftShowsPrec f' g'
    g'' = liftShowList f' g'
  
  
-- Block internal tree structure
data Node a = Closed a | Open (M.Map (Tag Id) (Node a))
  deriving (Eq, Functor, Foldable, Traversable)

emptyNode = Open M.empty


mergeNode :: Node a -> Node a -> Collect (PathError Id Tid) (Node a)
mergeNode (Open m)  (Open n)  = Open <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
mergeNode _         _         = (Collect . Left) (PathError M.empty)


instance Eq1 Node where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open ma)  (Open mb)  = liftEq (liftEq eq) ma mb
  liftEq _  _          _          = False

  
instance Show a => Show (Node a) where
  showsPrec = showsPrec1
  
  
instance Show1 Node where
  liftShowsPrec f g i e = case e of
    Closed a -> f i a
    Open m -> liftShowsPrec f' g' i m where
      f' = liftShowsPrec f g
      g' = liftShowList f g
  

instance Monoid (Collect (ExprErrors b) (Node a)) where
  mempty = pure emptyNode
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeNode a b))


-- Set expression tree
data RefScope = Enclosing | Current

data Ref a = Ref RefScope a

newtype STree a b = ST (M.Map a (Node (Ref b)))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree a b -> STree a b -> Collect (PathError Id a) (STree a b)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
  
  
instance Ord a => Monoid (Collect (ExprErrors a) (STree a b)) where
  mempty = pure emptySTree
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeSTree a b))

    
pathSTree :: Path Id a -> b -> STree a b
pathSTree path = tree path . Closed . Ref Current


punSTree :: Path Id Vid -> STree Vid (Expr Vid)
punSTree path = (tree (public <$> path) . Closed . Ref Enclosing) (varPath path) where
  public = either Pub (Pub . Label) . getvis
  
  varPath (Pure k) = Var k
  varPath (Free (p `Parser.At` x)) = varPath p `At` x


tree :: Path Id a -> Node (Ref b) -> STree a b
tree = go
  where
    go (Pure a)                     = ST . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
      
      
blockSTree :: STree Vid (Expr Vid) -> Expr Vid
blockSTree (ST m) =
  Block (M.elems en) se
  where
    (se, en) = M.foldrWithKey
      (\ k a (s, e) -> let a' = abstNode a in case k of
        Priv x -> (s, M.insert x a' e)
        Pub x  -> (M.insert x a' s, e))
      (M.empty, M.empty)
      m
        
    abstNode :: Node (Ref (Expr Vid))
      -> Node (E Expr Vid)
    abstNode (Closed (Ref Current e)) =
      (Closed . E . fmap Priv . abstract fenv) (abstractEither fself e)
    abstNode (Closed (Ref Enclosing e)) = Closed (lift e)
    abstNode (Open m) = Open (M.map abstNode m)
    
    fself :: Vid -> Either Tid Label
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
    
