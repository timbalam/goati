{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, StandaloneDeriving #-}
module Types.Expr
  ( Expr(..)
  , Eval(..)
  , Member(..)
  , Id(..)
  , Node(..)
  , STree, pathSTree, punSTree, blockSTree
  , Vid, Tid
  , ExprErrors
  , Label, Tag(..), Path, Vis(..), Sym(..)
  )
  where
  

import Types.Parser( Label, Tag(..), Path, Vis(..), getvis, Sym(..), getsym )
import qualified Types.Parser as Parser
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
data Eval a = Eval { getEval :: Either Vid (Expr a) }
  deriving (Eq, Show, Functor, Foldable, Traversable)

  
data Expr a =
    String T.Text
  | Number Double
  | Var a
  | Block [Node (Scope Int Member a)] (M.Map Tid (Node (Scope Int Member a)))
  | Expr a `At` Tid
  | Expr a `Fix` Tid
  | Expr a `Update` Expr a
  deriving (Eq, Show, Functor, Foldable, Traversable)

  
newtype Member a = Member { getMember :: Scope Tid Expr a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
 
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
  

instance Applicative Eval where
  pure = return
  (<*>) = ap

instance Monad Eval where
  return = Eval . return . Var
  
  Eval m >>= f = Eval (m >>= bindExpr) where
    bindExpr (String s)     = return (String s)
    bindExpr (Number d)     = return (Number d)
    bindExpr (Var a)        = getEval (f a)
    bindExpr (Block en se)  = return (Block
      ((map . fmap) (>>>= bindMember) en)
      ((M.map . fmap) (>>>= bindMember) se)) where
      bindMember e = case f e of
        Eval (Right e) -> Member (lift e)
    bindExpr (e `At` x)     = (`At` x) <$> bindExpr e
    bindExpr (e `Fix` x)    = (`Fix` x) <$> bindExpr e
    bindExpr (e `Update` w) = liftA2 Update (bindExpr e) (bindExpr w)
        
    
instance Eq1 Eval where
  liftEq eq (Eval ma) (Eval mb) = liftEq (liftEq eq) ma mb
  
instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  String s      >>= _ = String s
  Number d      >>= _ = Number d
  Var a         >>= f = f a
  Block en se   >>= f = Block
    ((map . fmap) (>>>= bindMember) en)
    ((M.map . fmap) (>>>= bindMember) se) where
    bindMember = Member . lift . f
  e `At` x      >>= f = (e >>= f) `At` x
  e `Fix` x     >>= f = (e >>= f) `Fix` x
  e `Update` w  >>= f = (e >>= f) `Update` (w >>= f)

instance Eq1 Expr where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
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
  liftEq _  _                   _               = False
   
   
instance Show1 Eval where
  liftShowsPrec f g i (Eval m) = showsUnaryWith (liftShowsPrec f' g') "Eval" i m where
    f' = liftShowsPrec f g
    g' = liftShowList f g
  
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Var a           -> showsUnaryWith f "Var" i a
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    e `At` x        -> showsBinaryWith fexpr showsPrec "At" i e x
    e `Fix` x       -> showsBinaryWith (liftShowsPrec f g)
      showsPrec "Fix" i e x
    e `Update` w    -> showsBinaryWith fexpr fexpr "Update" i e w
    where
      flist = liftShowsPrec fmtree gmtree
      fmap = liftShowsPrec fmtree gmtree
      fmtree = liftShowsPrec fsc gsc
      gmtree = liftShowList fsc gsc
      fsc = liftShowsPrec f g
      gsc = liftShowList f g
      fexpr = liftShowsPrec f g
  
  
-- Block internal tree structure
data Node a = Closed a | Open (M.Map (Tag Id) (Node a))
  deriving (Eq, Show, Functor, Foldable, Traversable)

emptyNode = Open M.empty


mergeNode :: Node a -> Node a -> Collect (PathError Id Tid) (Node a)
mergeNode (Open m)  (Open n)  = Open <$> unionAWith f m n where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
mergeNode _         _         = (Collect . Left) (PathError M.empty)


instance Eq1 Node where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open ma)  (Open mb)  = liftEq (liftEq eq) ma mb
  liftEq _  _          _          = False

  
instance Show1 Node where
  liftShowsPrec f g i e = case e of
    Closed a -> showsUnaryWith f "Closed" i a
    Open m -> showsUnaryWith (liftShowsPrec f' g') "Open" i m where
      f' = liftShowsPrec f g
      g' = liftShowList f g
  

instance Monoid (Collect (ExprErrors b) (Node a)) where
  mempty = pure emptyNode
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedMatch))
    (getCollect (liftA2 mergeNode a b))


-- Set expression tree
newtype STree a = ST (M.Map a (Node (Expr (Sym a))))

emptySTree = ST M.empty


mergeSTree :: Ord a => STree a -> STree a -> Collect (PathError Id a) (STree a)
mergeSTree (ST a) (ST b) = ST <$> unionAWith f a b where
  f k a b = first (PathError . M.singleton k) (mergeNode a b)
  
  
instance Ord a => Monoid (Collect (ExprErrors a) (STree a)) where
  mempty = pure emptySTree
  
  a `mappend` b = either
    (Collect . Left)
    (first (pure . OlappedSet))
    (getCollect (liftA2 mergeSTree a b))

    
pathSTree :: Path Id a -> Expr (Sym a) -> STree a
pathSTree path = tree path . Closed


punSTree :: Path Id a -> STree a
punSTree path = tree path emptyNode


tree :: Path Id a -> Node (Expr (Sym a)) -> STree a
tree = go
  where
    go (Pure a)                     = ST . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
      
      
blockSTree :: STree Vid -> Expr (Sym Label)
blockSTree (ST m) =
  Block (M.elems en) se
  where
    (se, en) = M.foldrWithKey
      (\ k a (s, e) -> let a' = abstNode k a in case k of
        Priv x -> (s, M.insert x a' e)
        Pub x  -> (M.insert x a' s, e))
      (M.empty, M.empty)
      m
        
    abstNode :: Vid -> Node (Expr (Sym Vid))
      -> Node (Scope Int Member (Sym Label))
    abstNode k (Closed e) = (Closed . abstract fenv . Member)
      (abstractEither fself e)
      
    abstNode _ (Open m) = Open (M.mapWithKey (abstNode . Pub) m)
    
    fself :: Sym Vid -> Either Tid (Sym Label)
    fself = traverse (\ e -> case e of
      Pub x                     -> Left x
      Priv l
        | M.member (Label l) se -> Left (Label l)
        | otherwise             -> Right l)
      
    fenv :: Sym Label -> Maybe Int
    fenv = either (const Nothing) (flip M.lookupIndex en) . getsym
    
  
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
