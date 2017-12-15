{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Core
  ( Eval(..)
  , Expr(..)
  , liftExpr
  , mapExpr
  , Enscope(..)
  , Id(..)
  , MRes(..)
  , M
  , pathM
  , blockM
  , S
  , declS
  , pathS
  , punS
  , blockS
  , Vis(..)
  , Label
  , Tag(..)
  , Path
  )
  where
  

import Types.Parser( Label, Tag(..), Path, Vis(..) )
import qualified Types.Parser as Parser
--import qualified Types.Error as E

import Control.Applicative ( liftA2 )
import Control.Monad ( join, ap )
import Control.Monad.Free
import Control.Monad.Trans
import Data.Monoid ( (<>) )
import Data.Functor.Classes
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import qualified Data.Text as T
import Bound


-- Interpreted my-language expression
newtype Eval a = Eval { getEval :: Maybe (Expr a) }
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
liftExpr :: Expr a -> Eval a
liftExpr = Eval . return


mapExpr :: (Expr a -> Expr b) -> Eval a -> Eval b
mapExpr f = Eval . fmap f . getEval
  
  
data Expr a =
    String T.Text
  | Number Double
  | Var a
  | Block [Enscope Eval a] (M.Map (Tag Id) (Enscope Eval a))
  | Expr a `Fix` Tag Id
  | Expr a `At` Tag Id
  | Expr a `Update` Expr a
  | Expr a `Concat` Eval a
  deriving (Eq, Show, Functor, Foldable, Traversable)
            
  
newtype Enscope m a = Enscope { getEnscope :: Scope Int (Scope (Tag Id) m) a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
 
data Id =
    BlockId Integer
  | StrId T.Text
  | FloatId Rational
  | IntId Integer
  deriving (Eq, Ord, Show)
  
  
instance Applicative Eval where
  pure = return
  (<*>) = ap

instance Monad Eval where
  return = Eval . return . return
  
  Eval Nothing  >>= _ = Eval Nothing
  Eval (Just v) >>= f = case v of
    String s        -> liftExpr (String s)
    Number d        -> liftExpr (Number d)
    Var e           -> f e
    Block en se     -> liftExpr (Block (map (>>>= f) en) (M.map (>>>= f) se))
    v `Fix` x       -> liftExpr v >>= mapExpr (`Fix` x) . f
    v `At` x        -> liftExpr v >>= mapExpr (`At` x) . f
    v1 `Update` v2  -> Eval (liftA2 Update (getEval (liftExpr v1 >>= f))  (getEval (liftExpr v2 >>= f)))
    v `Concat` e    -> liftExpr v >>= mapExpr (`Concat` (e >>= f)) . f
    
instance Eq1 Eval where
  liftEq eq (Eval ma) (Eval mb) = liftEq (liftEq eq) ma mb
  
instance Show1 Eval where
  liftShowsPrec f g i (Eval m) = showsUnaryWith (liftShowsPrec fval gval) "Eval" i m where
    fval = liftShowsPrec f g
    gval = liftShowList f g
      
    
    

instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  String s        >>= _ = String s
  Number d        >>= _ = Number d
  Var a           >>= f = f a
  Block en se     >>= f =
    Block (map (>>>= liftExpr . f) en) (M.map (>>>= liftExpr . f) se)
  v `At` x        >>= f = (v >>= f) `At` x
  v `Fix` x       >>= f = (v >>= f) `Fix` x
  v `Update` w    >>= f = (v >>= f) `Update` (w >>= f)
  v `Concat` e    >>= f = (v >>= f) `Concat` (e >>= liftExpr . f)
    
instance Eq1 Expr where
  liftEq eq (String sa)         (String sb)         = sa == sb
  liftEq eq (Number da)         (Number db)         = da == db
  liftEq eq (Var a)             (Var b)             = eq a b
  liftEq eq (Block ena sea)     (Block enb seb)     = 
    liftEq (liftEq eq) ena enb && liftEq (liftEq eq) sea seb
    
  liftEq eq (va `At` xa)        (vb `At` xb)        =
    liftEq eq va vb && xa == xb
    
  liftEq eq (va `Fix` xa)       (vb `Fix` xb)       =
    liftEq eq va vb && xa == xb
    
  liftEq eq (va `Update` wa)  (vb `Update` wb)  =
    liftEq eq va vb && liftEq eq wa wb
    
  liftEq eq (va `Concat` ea)  (vb `Concat` eb)  =
    liftEq eq va vb && liftEq eq ea eb
    
  liftEq _  _                   _                  = False
    
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Var a           -> showsUnaryWith f "Var" i a
    Block en se     -> showsBinaryWith flist fmap "Block" i en se
    v `At` x        -> showsBinaryWith fval showsPrec "At" i v x
    v `Fix` x       -> showsBinaryWith fval showsPrec "Fix" i v x
    v `Update` w    -> showsBinaryWith fval fval "Update" i v w
    v `Concat` e    -> showsBinaryWith fval fexpr "Concat" i v e
    where
      fval = liftShowsPrec f g
      flist = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
      fmap = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
      fexpr = liftShowsPrec f g

  
instance MonadTrans Enscope where
  lift = Enscope . lift . lift
  
instance Bound Enscope
  
    
-- Maybe wrapper with specialised Monoid instance
newtype MRes a = MRes { getresult :: Maybe a }
  deriving (Functor, Applicative, Monad)
  
  
-- Match expression tree
data M a = V a | Tr (M.Map (Tag Id) (M a))

emptyM = Tr M.empty


mergeM :: M a -> M a -> MRes (M a)
mergeM (Tr m) (Tr n)  = Tr <$> unionAWith mergeM m n
mergeM _      _       = MRes Nothing

instance Monoid (MRes (M a)) where
  mempty = pure emptyM
  
  a `mappend` b = join (liftA2 mergeM a b)


-- Set expression tree
data S a = S (M.Map a (M (Eval a)))

emptyS = S M.empty


mergeS :: Ord a => S a -> S a -> MRes (S a)    
mergeS (S a) (S b) = S <$> unionAWith mergeM a b
  
  
instance Ord a => Monoid (MRes (S a)) where
  mempty = pure emptyS
  
  a `mappend` b = join (liftA2 mergeS a b)
  

declS :: Path Id a -> S a
declS path = (tree path . V) (Eval Nothing)
  

pathS :: Path Id a -> Eval a -> S a
pathS path = tree path . V


punS :: Path Id a -> S a
punS path = tree path emptyM


tree :: Path Id a -> M (Eval a) -> S a
tree = go
  where
    go (Pure a)                     = S . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Tr . M.singleton x

  
pathM :: Path Id (Tag Id) -> a -> M a
pathM path = go path . V
  where
    go (Pure x)                     = Tr . M.singleton x
    go (Free (path `Parser.At` x))  = go path . Tr . M.singleton x
      

blockM :: Monoid m => (Eval a -> m) -> M (Eval a -> m) -> Eval a -> m
blockM _ (V f)  e = f e
blockM k (Tr m) e = k (mapExpr (\ v -> foldr (flip Fix) v (M.keys m)) e) <> go (Tr m) e
  where
    go :: Monoid m => M (Eval a -> m) -> Eval a -> m
    go (V f)  e = f e
    go (Tr m) e = M.foldMapWithKey (\ k -> flip go (mapExpr (`At` k) e)) m
  

blockS :: S (Vis Id) -> Expr (Vis Id)
blockS (S m) =
  Block (M.elems en) se
  where
    (se, en) =
      M.foldrWithKey
        (\ k a (s, e) -> let
          aen = abstM (return k) a
          ase = substitute k (lift (Eval Nothing)) aen
          in case k of
            Priv x -> (s, M.insert x aen e)
            Pub x -> (M.insert x ase s, e))
        (M.empty, M.empty)
        m
        
    abstM :: Eval (Vis Id) -> M (Eval (Vis Id)) -> Enscope Eval (Vis Id)
    abstM _ (V e) = (Enscope . abstract fenv . abstract fself) e
    abstM p (Tr m) = (wrap . liftExpr) (Block []
      (M.mapWithKey (\ k -> lift . unwrap . abstM (mapExpr (`At` k) p)) m)
      `Concat` unwrap (lift p')) where
      p' = mapExpr (\ v -> foldr (flip Fix) v (M.keys m)) p
      unwrap = unscope . unscope . getEnscope
      wrap = Enscope . Scope . Scope
        
    -- unscope (unscope (getEnscope (Enscope f a)))
    --  ~ unscope (unscope (Scope1 (Scope2 f) a)) 
    --  ~ unscope (Scope2 f (Var b1 (Scope2 f a)))
    --  ~ f (Var b2 (f (Var b1 (Scope2 f))))
        
        
    fself :: Vis Id -> Maybe (Tag Id)
    fself (Pub x)               = Just x
    fself (Priv l)
        | M.member (Label l) se = Just (Label l)
        | otherwise             = Nothing
      
      
    fenv :: Vis Id -> Maybe Int
    fenv (Pub _) = Nothing
    fenv (Priv l) = M.lookupIndex l en
        
  
  
unionAWith :: (Applicative f, Ord k) => (a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    (M.zipWithAMatched (\ _ -> f))
    
