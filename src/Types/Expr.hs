{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Types.Expr
  ( Expr(..), hoistExpr
  , Node(..)
  , E(..), toE, traverseScopeE, foldMapBoundE, foldMapBoundE'
  , Key(..), Var(..)
  , ListO(..), Lexpr
  , public, tag
  , Ref, currentRef, liftedRef
  , Build, buildSym, buildPath, buildPun, buildVar, blockBuild
  , BuildN, buildNPath, matchBuild
  , ExprError(..), ExprErrors, Paths(..), listPaths
  , Label, Unop(..), Binop(..)
  , module Types.Prim
  )
  where
  

import Types.Parser( Label, Unop(..), Binop(..) )
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
data Expr s k a =
    Number Double
  | String T.Text
  | Bool Bool
  | Var a
  | Block (Block s k a)
  | Expr s k a `At` k
  | Expr s k a `Fix` k
  | Expr s k a `Update` Expr s k a
  | Expr s k a `AtPrim` PrimTag
  deriving (Functor, Foldable, Traversable)
  
  
hoistExpr :: Functor (s k) => (forall x. s k x -> s' k x) -> Expr s k a -> Expr s' k a
hoistExpr f = go where 

  go (Number d) = Number d
  go (String t) = String t
  go (Bool b) = Bool b
  go (Var a) = Var a
  go (Block b) = Block (hoistBlock f b)
  go (e `At` k) = go e `At` k
  go (e `Fix` k) = go e `Fix` k
  go (e `Update` w) = go e `Update` go w
  go (e `AtPrim` p) = go e `AtPrim` p
  
  
block :: [Node s k (E k (Expr s k) a)] -> (s k (Node s k (E k (Expr s k) a))) -> Expr s k a
block en se = Block (B_ en se)

  
data Block s k a = B_ [Node s k (E k (Expr s k) a)] (s k (Node s k (E k (Expr s k) a)))
  deriving (Functor, Foldable, Traversable)
  
  
hoistBlock :: Functor (s k) => (forall x . s k x -> s' k x) -> Block s k a -> Block s' k a
hoistBlock f (B_ en se) = (B_ (map f' en) . f) (f' <$> se) where
    f' = hoistNode f . (hoistE (hoistExpr f) <$>)
  
  
-- | Free with generalised Eq1 and Show1 instances
data Node s k a = 
    Closed a
  | Open (s k (Node s k a))
  deriving (Functor, Foldable, Traversable)
  
  
hoistNode :: Functor (s k) => (forall x. s k x -> s' k' x) -> Node s k a -> Node s' k' a
hoistNode f (Closed a) = Closed a
hoistNode f (Open s) = (Open . f) (hoistNode f <$> s)
  
  
newtype E k m a = E { unE :: Scope Int (Scope k m) a }
  deriving (Eq, Eq1, Functor, Foldable, Traversable, Applicative, Monad)
  

toE :: Monad m => m (Var k (Var Int a)) -> E k m a
toE = E . toScope . toScope


hoistE :: Functor f => (forall x . f x -> g x) -> E k f a -> E k g a
hoistE f (E s) = E (hoistScope (hoistScope f) s)


foldMapBoundE' :: (Traversable m, Monoid r) => (b -> r) -> E b m a -> r
foldMapBoundE' f = getConst . traverseScopeE (Const . f) pure


foldMapBoundE :: (Foldable m, Monoid r) => (b -> r) -> E b m a -> r
foldMapBoundE f (E s) =
  foldMapScope f (\ v -> case v of
    B i -> mempty
    F a -> foldMapBound f a) (unscope s)


traverseScopeE :: (Applicative f, Traversable m) => (k -> f k') -> (a -> f a') -> E k m a -> f (E k' m a')
traverseScopeE f g (E s) = E <$> bitransverseScope (traverseScope f) g s
  -- traverseScope f :: (a -> f a') -> Scope k m a -> f (Scope k' m a')


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
instance Functor (s k) => Applicative (Expr s k) where
  pure = return
  
  (<*>) = ap
  
instance Functor (s k) => Monad (Expr s k) where
  return = Var
  
  String s          >>= _ = String s
  Number d          >>= _ = Number d
  Bool b            >>= _ = Bool b
  Var a             >>= f = f a
  Block (B_ en se)  >>= f = Block (B_
    ((map . fmap) (>>>= f) en)
    ((fmap . fmap) (>>>= f) se))
  e `At` x          >>= f = (e >>= f) `At` x
  e `Fix` m         >>= f = (e >>= f) `Fix` m
  e `Update` w      >>= f = (e >>= f) `Update` (w >>= f)
  e `AtPrim` x      >>= f = (e >>= f) `AtPrim` x
    

instance Bitraversable s => Bifunctor (Expr s) where
  bimap = bimapDefault
  
  
instance Bitraversable s => Bifoldable (Expr s) where
  bifoldMap = bifoldMapDefault


instance Bitraversable s => Bitraversable (Expr s) where
  bitraverse f g = go where
    
    go (Number d) = pure (Number d)
    go (String s) = pure (String s)
    go (Bool b) = pure (Bool b)
    go (Var a) = Var <$> g a
    go (Block b) = Block <$> bitraverse f g b
    go (e `At` k) = liftA2 At (go e) (f k)
    go (e `Fix` k) = liftA2 Fix (go e) (f k)
    go (e `Update` w) = liftA2 Update (go e) (go w)
    go (e `AtPrim` x) = (`AtPrim` x) <$> go e

  
instance (Functor (s k), Eq1 (s k), Eq k, Eq a) => Eq (Expr s k a) where
  (==) = eq1
  
  
instance (Functor (s k), Eq1 (s k), Eq k) => Eq1 (Expr s k) where
  liftEq _  (String sa)       (String sb)       = sa == sb
  liftEq _  (Number da)       (Number db)       = da == db
  liftEq _  (Bool ba)         (Bool bb)         = ba == bb
  liftEq eq (Var a)           (Var b)           = eq a b
  liftEq eq (Block ba)        (Block bb)        = liftEq eq ba bb
  liftEq eq (ea `At` xa)      (eb `At` xb)      =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)     (eb `Fix` xb)     =
    liftEq eq ea eb && xa == xb
  liftEq eq (ea `Update` wa)  (eb `Update` wb)  =
    liftEq eq ea eb && liftEq eq wa wb
  liftEq eq (ea `AtPrim` xa)  (eb `AtPrim` xb)         =
    liftEq eq ea eb && xa == xb
  liftEq _  _                   _               = False
   
   
instance (Functor (s k), Show1 (s k), Show k, Show a) => Show (Expr s k a) where
  showsPrec = showsPrec1
   
   
instance (Functor (s k), Show1 (s k), Show k) => Show1 (Expr s k) where
  liftShowsPrec = go where 
    
    go :: forall a. (Int -> a -> ShowS) -> ([a] -> ShowS) -> Int -> Expr s k a -> ShowS
    go f g i e = case e of
      String s          -> showsUnaryWith showsPrec "String" i s
      Number d          -> showsUnaryWith showsPrec "Number" i d
      Bool b            -> showsUnaryWith showsPrec "Bool" i b
      Var a             -> showsUnaryWith f "Var" i a
      Block (B_ en se)  -> showsBinaryWith f''' f''' "block" i en se
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
        
        
-- | Block instances 
instance Bitraversable s => Bifunctor (Block s) where
  bimap = bimapDefault
    
    
instance Bitraversable s => Bifoldable (Block s) where
  bifoldMap = bifoldMapDefault
    

instance Bitraversable s => Bitraversable (Block s) where
  bitraverse f g (B_ es se) = liftA2 B_ (traverse fg' es) (bitraverse f fg' se) where
    fg' = bitraverse f (bitraverseE f g)
    
  
instance (Functor (s k), Eq1 (s k), Eq k, Eq a) => Eq (Block s k a) where
  (==) = eq1
  
  
instance (Functor (s k), Eq1 (s k), Eq k) => Eq1 (Block s k) where
  liftEq eq (B_ ena sea) (B_ enb seb) =
    liftEq eq' ena enb && liftEq eq' sea seb where
      eq' = liftEq (liftEq eq)
        
        
-- | Node instances
instance Bitraversable s => Bifunctor (Node s) where
  bimap = bimapDefault
  
  
instance Bitraversable s => Bifoldable (Node s) where
  bifoldMap = bifoldMapDefault
  
  
instance Bitraversable s => Bitraversable (Node s) where
  bitraverse f g = go where
    
    go (Closed a) = Closed <$> g a
    go (Open s)   = Open <$> bitraverse f go s
  

instance Eq1 (s k) => Eq1 (Node s k) where
  liftEq eq (Closed a) (Closed b) = eq a b
  liftEq eq (Open fa)  (Open fb)  = liftEq (liftEq eq) fa fb
  liftEq _  _           _         = False
  
  
instance (Eq (s k (Node s k a)), Eq a) => Eq (Node s k a) where
  Closed a == Closed b = a == b
  Open fa  == Open fb  = fa == fb
  _        == _        = False
 

instance Show1 (s k) => Show1 (Node s k) where
  liftShowsPrec f g i (Closed a) = showsUnaryWith f "Closed" i a
  liftShowsPrec f g i (Open m) = showsUnaryWith f'' "Open" i m where
    f'' = liftShowsPrec f' g'
    g' = liftShowList f g
    f' = liftShowsPrec f g
    
    
instance (Show (s k (Node s k a)), Show a) => Show (Node s k a) where
  showsPrec d (Closed a) = showParen (d > 10)
    (showString "Closed " . showsPrec 11 a)
  showsPrec d (Open s) = showParen (d > 10)
    (showString "Open " . showsPrec 11 s)

  
bitraverseFree
  :: (Bitraversable t, Applicative f)
  => (a -> f a')
  -> (b -> f b')
  -> Free (t a) b
  -> f (Free (t a') b')
bitraverseFree f = bitransverseFree (bitraverse f)


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
data Key b k =
    Label Label
  | Symbol k
  | Id b
  | Unop Unop
  | Binop Binop
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
      
    
tag :: Parser.Tag -> Key b Parser.Symbol
tag (Parser.Label l) = Label l
tag (Parser.Symbol s) = Symbol s
  

instance Applicative (Key b) where
  pure = return
  
  (<*>) = ap
  
  
instance Monad (Key b) where
  return = Symbol
  
  Label l  >>= _ = Label l
  Symbol k >>= f = f k
  Id i     >>= _ = Id i
  Unop op  >>= _ = Unop op
  Binop op >>= _ = Binop op
  
  
instance Bifunctor Key where
  bimap = bimapDefault
  
  
instance Bifoldable Key where
  bifoldMap = bifoldMapDefault
  
  
instance Bitraversable Key where
  bitraverse f g k = case k of
    Label l -> pure (Label l)
    Symbol k -> Symbol <$> g k
    Id i -> Id <$> f i
    Unop op -> pure (Unop op)
    Binop op -> pure (Binop op)
  
        
-- | ListO
newtype ListO k a = ListO { getListO :: [(k, a)] }
  deriving (Show, Functor, Foldable, Traversable)
  
  
instance Bifunctor ListO where
  bimap f g (ListO xs) = ListO (bimap f g <$> xs)
  
  
instance Bifoldable ListO where
  bifoldMap f g (ListO xs) = foldMap (bifoldMap f g) xs
  
  
instance Bitraversable ListO where
  bitraverse f g (ListO xs) = ListO <$> traverse (bitraverse f g) xs
  
  
instance (Ord k, Eq a) => Eq (ListO k a) where
  (==) = eq1

  
instance Ord k => Eq1 (ListO k) where
  liftEq eq (ListO a) (ListO b) = liftEq (liftEq eq) (sortOn fst a) (sortOn fst b)
  

instance Show k => Show1 (ListO k) where
  liftShowsPrec f g i (ListO xs) = showsUnaryWith f' "ListO" i xs where
    f' _ = liftShowList f g
    
    
type Lexpr k = Expr ListO (Key Int k)


type Lnode k = Node ListO (Key Int k)

  
-- Block field tree builder
data Build a = Build
  { symbols :: M.Map Parser.Symbol Int
  , fields :: M.Map Parser.Var (BuildN (Ref a))
  }
  
data Ref a = R RefType a
  deriving (Functor)

data RefType = Current | Lifted

currentRef :: a -> Ref a
currentRef = R Current

liftedRef :: a -> Ref a
liftedRef = R Lifted
  
  
type BuildN = Node M.Map Parser.Tag

  
emptyBuild = Build M.empty M.empty
    
emptyBuildN :: Node M.Map k a
emptyBuildN = Open M.empty
      
  
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
    fnode k a b = first (pure . OlappedSet k) (mergeBuildN a b)
    fsyms k _ _ = (collect . pure) (OlappedSym k)


mergeBuildN :: BuildN a -> BuildN a -> Collect Paths (BuildN a)
mergeBuildN (Open m) (Open n) =
  Open <$> unionAWith f m n where
    f k a b = first (Paths . M.singleton k) (mergeBuildN a b)
    
mergeBuildN _ _ =
  collect (Paths M.empty)
  

instance Monoid (Collect ExprErrors (Build a)) where
  mempty = pure emptyBuild
  
  a `mappend` b = (either
    collect
    id
    . getCollect) (liftA2 mergeBuild a b)
    
    
instance Monoid (Collect ExprErrors (BuildN a)) where
  mempty = pure emptyBuildN
  
  a `mappend` b = (either
    collect
    (first (pure . OlappedMatch))
    . getCollect) (liftA2 mergeBuildN a b)
    
    
-- | nested match tree builder
buildNPath :: Parser.Path Parser.Tag -> a -> BuildN a
buildNPath path = go path . Closed
  where
    go (Pure x)                     = Open . M.singleton x
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x
        
        
matchBuild
  :: (Monoid m, Functor f)
  => (f (Expr s (Key b Parser.Symbol) a) -> m)
  -> BuildN (f (Expr s (Key b Parser.Symbol) a) -> m)
  -> f (Expr s (Key b Parser.Symbol) a)
  -> m
matchBuild _ (Closed f) e = f e
matchBuild k b@(Open m) e = k ((flip . foldr) (flip Fix . tag) (M.keys m) <$> e)
  `mappend` go b e where
    go
      :: (Monoid m, Functor f)
      => BuildN (f (Expr s (Key b Parser.Symbol) a) -> m)
      -> f (Expr s (Key b Parser.Symbol) a)
      -> m
    go (Closed f) = f
    go (Open m) = M.foldMapWithKey
      (\ k b -> go b . ((`At` tag k) <$>))
      m
  
    
-- | block field tree builder
buildSym :: Parser.Symbol -> Build a
buildSym s = Build (M.singleton s 0) M.empty


buildVar :: Parser.Path Label -> Build (Expr s (Key b Parser.Symbol) Parser.Var)
buildVar l = (buildPath (Parser.Priv <$> l) . currentRef . exprPath) (Parser.Pub . Parser.Label <$> l)


buildPun
  :: Parser.Path Parser.Var
  -> Build (Expr s (Key b Parser.Symbol) Parser.Var)
buildPun path =
  (buildPath (Parser.Pub . public <$> path) . liftedRef) (exprPath path)
  
  
exprPath :: Parser.VarPath -> Expr s (Key b Parser.Symbol) Parser.Var
exprPath (Pure a) = Var a
exprPath (Free (p `Parser.At` t)) = exprPath p `At` tag t
    
    
public :: Parser.Var -> Parser.Tag
public (Parser.Pub t) = t
public (Parser.Priv l) = Parser.Label l


buildPath :: Parser.Path Parser.Var -> Ref a -> Build a
buildPath p = go p . Closed
  where
    go (Pure a)                     = Build M.empty . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Open . M.singleton x

      
blockBuild :: Build (Lexpr Parser.Symbol Parser.Var) -> Lexpr Parser.Symbol Parser.Var
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
      
    buildO :: M.Map Parser.Tag a -> ListO (Key Int Parser.Symbol) a
    buildO m = (ListO . map (first tag)) (M.toAscList m)
        
    abstRef
      :: Functor (s (Key Int Parser.Symbol))
      => Ref (Expr s (Key Int Parser.Symbol) Parser.Var)
      -> E (Key Int Parser.Symbol) (Expr s (Key Int Parser.Symbol)) Parser.Var
    abstRef (R Current e) =
      (E . fmap Parser.Priv . abstract fenv) (abstractEither fself e)
    abstRef (R Lifted e) = lift e
    
    fself :: Parser.Var -> Either (Key Int Parser.Symbol) Label
    fself = \ e -> case e of
      Parser.Pub t              -> Left (tag t)
      Parser.Priv l
        | M.member (Label l) se -> Left (Label l)
        | otherwise             -> Right l
      
    fenv :: Label -> Maybe Int
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
    
