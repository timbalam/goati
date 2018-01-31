{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Types.Expr
  ( Expr(..), hoistExpr
  , Node(..)
  , Field(..), toField
  , Key(..), Var(..)
  , ListO(..), Lexpr
  , public, tag
  , Ref, currentRef, liftedRef
  , Build, buildSym, buildPath, buildPun, buildVar, blockBuild
  , Node, matchPath, buildMatch
  , ExprError(..), ExprErrors, Paths(..), listPaths
  , Ident, Unop(..), Binop(..)
  , module Types.Prim
  )
  where
  

import Types.Parser( Ident, Unop(..), Binop(..) )
import qualified Types.Parser as Parser
import Types.Prim
import Util(  Collect(..), collect )

import Control.Applicative ( liftA2, Const(..) )
import Control.Monad ( join, ap, (>=>) )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Functor.Identity
--import Data.Monoid ( (<>) )
import Data.Semigroup
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Typeable
import Data.Functor.Classes
import Data.List.NonEmpty( NonEmpty, nonEmpty )
import Data.List( sortOn )
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import qualified Data.Set as S
import Bound
import Bound.Scope
  ( abstractEither
  , hoistScope
  , traverseScope
  , bitransverseScope
  , foldMapScope
  , foldMapBound )


-- Interpreted my-language expression
data Expr a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block [Node (Field Expr a)] (M.Map Key (Node (Field Expr a)))
  | Expr a `At` Key
  | Expr a `Fix` Key
  | Expr a `Update` Expr a
  | Expr a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
-- | Free with generalised Eq1 and Show1 instances
data Node a = 
    Closed a
  | Open (M.Map Key (Node a))
  deriving (Functor, Foldable, Traversable)
  
  
newtype Field m a = Field { getField :: Scope Int (Scope Key m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toField :: Monad m => m (Var k (Var Int a)) -> Field k m a
toField = Field . toScope . toScope


hoistField :: Functor f => (forall x . f x -> g x) -> Field f a -> Field g a
hoistField f (Field s) = Field (hoistScope (hoistScope f) s)

  
-- | Expr instances
instance Applicative Expr where
  pure = return
  
  (<*>) = ap
  
instance Monad Expr where
  return = Var
  
  String s          >>= _ = String s
  Number d          >>= _ = Number d
  Bool b            >>= _ = Bool b
  Var a             >>= f = f a
  Block en se       >>= f = Block (B_
    ((map . fmap) (>>>= f) en)
    ((fmap . fmap) (>>>= f) se))
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` w      >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x      >>= f = (e >>= f) `AtPrim` x
    
  
instance Eq a => Eq (Expr a) where
  (==) = eq1
  
  
instance Eq1 Expr where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ena sea)   (Block enb seb)   =
    liftEq f ena enb && liftEq f sea seb where
    f = liftEq (liftEq eq)
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (ea `AtPrim` xa)  (eb `AtPrim` xb)         =
    liftEq eq ea eb && xa == xb
  liftEq _  _                   _               = False
   
   
instance Show a => Show (Expr a) where
  showsPrec = showsPrec1
   
   
instance Show1 Expr where
  liftShowsPrec = go where 
    
    go :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr s k a -> ShowS
    go f g i e = case e of
      String s          -> showsUnaryWith showsPrec "String" i s
      Number d          -> showsUnaryWith showsPrec "Number" i d
      Bool b            -> showsUnaryWith showsPrec "Bool" i b
      Var a             -> showsUnaryWith f "Var" i a
      Block en se       -> showsBinaryWith f''' f''' "Block" i en se
      e `At` x          -> showsBinaryWith f' showsPrec "At" i e x
      e `Fix` x         -> showsBinaryWith f' showsPrec "Fix" i e x
      e `Update` w      -> showsBinaryWith f' f' "Update" i e w
      e `AtPrim` p      -> showsBinaryWith f' showsPrec "AtPrim" i e p
      where
        f''' :: (Show1 f, Show1 g, Show1 h) => Int -> f (g (h a)) -> ShowS
        f''' = liftShowsPrec f'' g''
        
        f'' :: (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
        f'' = liftShowsPrec f' g'
        
        g'' :: (Show1 f, Show1 g) => [f (g a)] -> ShowS
        g'' = liftShowList f' g'
        
        f' :: Show1 f => Int -> f a -> ShowS
        f' = liftShowsPrec f g
        
        g' :: Show1 f => [f a] -> ShowS
        g' = liftShowList f g
        
        
-- | Node instances
instance Eq1 Node where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False
  
  
instance (Eq a) => Eq (Node a) where
  Closed a == Closed b = a == b
  Open fa  == Open fb  = fa == fb
  _        == _        = False
 

instance Show1 Node where
  liftShowsPrec f g i (Closed a) = showsUnaryWith f "Closed" i a
  liftShowsPrec f g i (Open m) = showsUnaryWith f'' "Open" i m where
    f'' = liftShowsPrec f' g'
    g' = liftShowList f g
    f' = liftShowsPrec f g
    
    
instance (Show a) => Show (Node a) where
  showsPrec d (Closed a) = showParen (d > 10)
    (showString "Closed " . showsPrec 11 a)
  showsPrec d (Open s) = showParen (d > 10)
    (showString "Open " . showsPrec 11 s)
    

-- | Field instances
instance MonadTrans (Field k) where
  lift = Field . lift . lift
  
  
instance Bound (Field k)
  
  
instance (Monad m, Show1 m, Show a) => Show (Field m a) where
  showsPrec = showsPrec1
    
    
instance (Monad m, Show1 m) => Show1 (Field m) where
  liftShowsPrec f g i m =
    (showsUnaryWith f''' "toE" i . fromScope . fromScope) (unE m) where
    f''' = liftShowsPrec  f'' g''
      
    f' = liftShowsPrec f g
    g' = liftShowList f g
    
    f'' = liftShowsPrec f' g'
    g'' = liftShowList f' g'
    
    

-- | Expression key type
data Key =
    Ident Ident
  | Id Int
  | Unop Unop
  | Binop Binop
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
      
    
tag :: Parser.Tag -> State Int Key
tag (Parser.Ident l) = Ident l
tag (Parser.Symbol s) = state (\ i -> (succ i, Symbol i))
  
  
-- Block field tree builder
data Build a = Build
  { symbols :: M.Map Parser.Symbol Int
  , fields :: M.Map Parser.Var (Node (Ref a))
  }
  
data Ref a = R RefType a
  deriving (Functor)

data RefType = Current | Lifted

currentRef :: a -> Ref a
currentRef = R Current

liftedRef :: a -> Ref a
liftedRef = R Lifted

  
emptyBuild = Build M.empty M.empty
    
emptyNode :: Node a
emptyNode = Open M.empty
      
  
-- | Errors when building block field tree
data ExprError =
    OlappedMatch Paths
  | OlappedSet Parser.Var Paths
  | OlappedSym Parser.Symbol
  deriving (Eq, Show, Typeable)
  
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
  liftA2 Build (unionAWith fsyms sa sb) (unionAWith fnode ma mb)
  where
    fnode k a b = first (pure . OlappedSet k) (mergeNode a b)
    fsyms k _ _ = (collect . pure) (OlappedSym k)


mergeNode :: Node a -> Node a -> Collect Paths (Node a)
mergeNode (Open m) (Open n) =
  Open <$> unionAWith f m n where
    f k a b = first (Paths . M.singleton k) (mergeNode a b)
    
mergeNode _ _ =
  collect (Paths M.empty)
  

instance Monoid (Collect ExprErrors (Build a)) where
  mempty = pure emptyBuild
  
  a `mappend` b = (either
    collect
    id
    . getCollect) (liftA2 mergeBuild a b)
    
    
instance Monoid (Collect ExprErrors (Node a)) where
  mempty = pure emptyNode
  
  a `mappend` b = (either
    collect
    (first (pure . OlappedMatch))
    . getCollect) (liftA2 mergeNode a b)
    
    
-- | nested match tree builder
matchPath :: Parser.Path Parser.Tag -> a -> Node a
matchPath path = go path . Closed
  where
    go (Pure x)                     = Open . M.singleton x
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
        
        
buildMatch
  :: (Monoid m, Functor f)
  => (f (Expr a) -> m)
  -> Node (f (Expr a) -> m)
  -> f (Expr a)
  -> m
buildMatch _ (Closed f) e = f e
buildMatch k b@(Open m) e = k ((flip . foldr) (flip Fix . tag) (M.keys m) <$> e)
  `mappend` go b e where
    go
      :: (Monoid m, Functor f)
      => Node (f (Expr a) -> m)
      -> f (Expr a)
      -> m
    go (Closed f) = f
    go (Open m) = M.foldMapWithKey
      (\ k b -> go b . ((`At` tag k) <$>))
      m
  
    
-- | block field tree builder
buildSym :: Parser.Symbol -> Build a
buildSym s = Build (M.singleton s 0) M.empty


buildVar :: Parser.Path Ident -> Build (Expr Parser.Var)
buildVar l = (buildPath (Parser.Priv <$> l) . currentRef . exprPath) (Parser.Pub . Parser.Ident <$> l)


buildPun
  :: Parser.Path Parser.Var
  -> Build (Expr Parser.Var)
buildPun path =
  (buildPath (Parser.Pub . public <$> path) . liftedRef) (exprPath path)
  
  
exprPath :: Parser.VarPath -> Expr Parser.Var
exprPath (Pure a) = Var a
exprPath (Free (p `Parser.At` t)) = exprPath p `At` tag t
    
    
public :: Parser.Var -> Parser.Tag
public (Parser.Pub t) = t
public (Parser.Priv l) = Parser.Ident l


buildPath :: Parser.Path Parser.Var -> Ref a -> Build a
buildPath p = go p . Closed
  where
    go (Pure a)                     = Build M.empty . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x

      
blockBuild :: Build (Expr Parser.Var) -> Expr Parser.Var
blockBuild (Build syms m) =
  first (>>= fsym) (block (M.elems en) (ListO pub))
  where
    (priv, pub) = (partitionVis . M.toAscList) (M.map (hoistNode buildO . fmap abstRef) m)
    
    se = M.fromAscList pub
    en = M.fromAscList priv
      
    partitionVis = foldr
      (\ (k, a) (priv, pub) -> case k of
        Parser.Priv l -> ((l, a):priv, pub)
        Parser.Pub t -> (priv, (tag t :: Key Int Parser.Symbol, a):pub))
      ([], [])
      
    buildO :: M.Map Parser.Tag a -> State Int (M.Map Key a)
    buildO = bitraverse tag id
        
    abstRef
      :: Functor (s (Key Int Parser.Symbol))
      => Ref (Expr s (Key Int Parser.Symbol) Parser.Var)
      -> Field Expr Parser.Var
    abstRef (R Current e) =
      (Field . fmap Parser.Priv . abstract fenv) (abstractEither fself e)
    abstRef (R Lifted e) = lift e
    
    fself :: Parser.Var -> Either (Key Int Parser.Symbol) Ident
    fself = \ e -> case e of
      Parser.Pub t              -> Left (tag t)
      Parser.Priv l
        | M.member (Ident l) se -> Left (Ident l)
        | otherwise             -> Right l
      
    fenv :: Ident -> Maybe Int
    fenv = flip M.lookupIndex en
    
    fsym :: Parser.Symbol -> Key Int Parser.Symbol
    fsym k = case M.lookupIndex k syms of
      Nothing -> Symbol k
      Just i -> Id i
  
  
unionAWith :: (Applicative f, Ord k) => (k -> a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched f)
    
