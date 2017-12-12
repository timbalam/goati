{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Core
  ( Expr(..)
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
  , Tag
  , Path
  , Env
  , Self
  )
  where
  

import Types.Parser( Label, Tag, Path, Vis(..) )
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


data Id =
    BlockLit Integer
  | StrLit T.Text
  | FloatLit Rational
  | IntLit Integer
  deriving (Eq, Ord, Show)

-- Interpreted my-language expression
data Expr a =
    String T.Text
  | Number Double
  | Var a
  | Undef
  | Block Id [Env Self a] (M.Map (Tag Id) (Env (Scope () Self) a))
  | Expr a `At` Tag Id
  | Expr a `Fix` Tag Id
  | Expr a `Update` Expr a
  | Expr a `Concat` Expr a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
  
  
type Env = Scope Int
type Self = Scope (Tag Id) Expr


instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  String s        >>= _ = String s
  Number d        >>= _ = Number d
  Var a           >>= f = f a
  Undef           >>= _ = Undef
  Block en se     >>= f = Block (map (>>>>= f) en) (M.map (>>>>= lift . f) se) where
    a >>>>= f = a >>>= lift . f
  e `At` x        >>= f = (e >>= f) `At` x
  e `Fix` x       >>= f = (e >>= f) `Fix` x
  e1 `Update` e2  >>= f = (e1 >>= f) `Update` (e2 >>= f)
  e1 `Concat` e2  >>= f = (e1 >>= f) `Concat` (e2 >>= f)
    
instance Eq1 Expr where
  liftEq eq (String sa)         (String sb)         = sa == sb
  liftEq eq (Number da)         (Number db)         = da == db
  liftEq eq (Var a)             (Var b)             = eq a b
  liftEq eq Undef               Undef               = True
  liftEq eq (Block ena sea)     (Block enb seb)     = liftEq (liftEq eq) ena enb && liftEq (liftEq eq) sea seb
  liftEq eq (ea `At` xa)        (eb `At` xb)        = liftEq eq ea eb && xa == xb
  liftEq eq (ea `Fix` xa)       (eb `Fix` xb)       = liftEq eq ea eb && xa == xb
  liftEq eq (e1a `Update` e2a)  (e1b `Update` e2b)  = liftEq eq e1a e1b && liftEq eq e2a e2b
  liftEq eq (e1a `Concat` e2a)  (e1b `Concat` e2b)  = liftEq eq e1a e1b && liftEq eq e2a e2b
  liftEq _  _                    _                  = False
    
instance Show1 Expr where
  liftShowsPrec f g i e = case e of
    String s        -> showsUnaryWith showsPrec "String" i s
    Number d        -> showsUnaryWith showsPrec "Number" i d
    Var a           -> showsUnaryWith f "Var" i a
    Undef           -> showString "Undef"
    Block en se     -> showsBinaryWith f1 f2 "Block" i en se where
      f1 = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
      f2 = liftShowsPrec (liftShowsPrec f g) (liftShowList f g)
    e `At` x        -> showsBinaryWith f' showsPrec "At" i e x
    e `Fix` x       -> showsBinaryWith f' showsPrec "Fix" i e x
    e1 `Update` e2  -> showsBinaryWith f' f' "Update" i e1 e2
    e1 `Concat` e2  -> showsBinaryWith f' f' "Concat" i e1 e2
    where
      f' = liftShowsPrec f g
  
    
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
data S a = S (M.Map a (M (Expr a)))

emptyS = S M.empty


mergeS :: Ord a => S a -> S a -> MRes (S a)    
mergeS (S a) (S b) =
  S <$> unionAWith mergeM a b
  
  
instance Ord a => Monoid (MRes (S a)) where
  mempty = pure emptyS
  
  a `mappend` b = join (liftA2 mergeS a b)
  

declS :: Path a -> S a
declS path = tree path (V Undef)
  

pathS :: Path a -> Expr a -> S a
pathS path = tree path . V


punS :: Path a -> S a
punS path = tree path emptyM


tree :: Path a -> M (Expr a) -> S a
tree = go
  where
    go (Pure a) =
      S . M.singleton a
      
    go (Free (path `Parser.At` x)) =
      go path . Tr . M.singleton x

  
pathM :: Path Tag -> a -> M a
pathM path = go path . V
  where
    go (Pure x) =
      Tr . M.singleton x

    go (Free (path `Parser.At` x)) =
      go path . Tr . M.singleton x
      

blockM :: Monoid m => (Expr a -> m) -> M (Expr a -> m) -> Expr a -> m
blockM rest = go1
  where
    --go1, go :: Monoid m => M (Expr a -> m) -> Expr a -> m
    go1 (V f) e = f e 
    
    go1 (Tr m) e =
      (rest . foldr (flip Fix) e) (M.keys m) <> go (Tr m) e
    
    
    go (V f) e = f e
    
    go (Tr m) e =
      M.foldMapWithKey (flip go . At e) m
  

blockS :: S (Vis Tag) -> Expr (Vis Tag)
blockS (S m) =
  Block (M.elems en) se
  where
    (se, en) =
      M.foldrWithKey
        (\ k a (s, e) -> let a' = intoSelf k a in
          case k of
            Priv x -> (s, M.insert x (abstEnv en a') e)
            Pub x -> ((M.insert x . abstEnv en) (abstract1 (Pub x) a') s, e))
        (M.empty, M.empty)
        m
      
      
    intoSelf :: Vis Id -> M (Expr (Vis Id)) -> Self (Vis Id)
    intoSelf _ (V e)   = abstSelf e
    intoSelf k (Tr m)  = (liftConcat ek . abstSelf) (Block [] m')
      where
      ek = foldr (flip Fix) (Var k) (M.keys m)
      m' = M.mapWithKey liftExpr m
        
      
    abstSelf :: Monad f => f (Vis Id) -> Scope (Tag Id) f (Vis Id)
    abstSelf = abstract (\ e -> case e of
      Pub x                     -> Just x
      Priv l
        | M.member (Label l) se -> Just (Label l)
        | otherwise             -> Nothing)
      
      
    abstEnv :: Monad f => f (Vis Id) -> Scope Int f (Vis Id)
    abstEnv = abstract (\ e -> case e of 
      Pub _  -> Nothing
      Priv l -> M.lookupIndex l en)
      
      
    liftExpr :: Label ->  M (Expr (Vis Id)) -> Env (Scope () Self) (Vis Id)
    liftExpr _ (V e) = (lift . lift) (lift e)
    liftExpr k (Tr m) = (lift . abstract1 (Pub k) . liftConcat ek . lift) (Block [] m') where
      ek = (foldr (flip Fix) . Var) (Pub k) (M.keys m)
      m' = M.mapWithKey liftExpr m
      
      
    liftConcat :: Expr a -> Scope b Expr a -> Scope b Expr a
    liftConcat e m = (Scope . (Concat (unscope m) . return)) (F e)
        
  
  
unionAWith :: (Applicative f, Ord k) => (a -> a -> f a) -> M.Map k a -> M.Map k a -> f (M.Map k a)
unionAWith f =
  (M.mergeA
    M.preserveMissing
    M.preserveMissing
    . M.zipWithAMatched) (\ _ -> f)
    
