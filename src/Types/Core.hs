{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving #-}
module Types.Core
  ( Expr(..)
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
  | Block [Enscope Expr a] (M.Map (Tag Id) (Enscope Expr a))
  | Expr a `At` Tag Id
  | Expr a `Fix` Tag Id
  | Expr a `Update` Expr a
  | Expr a `Concat` Expr a
  deriving (Eq, Show, Functor, Foldable, Traversable)
 
  
newtype Enscope m a = Enscope { getEnscope :: Scope Int (Scope (Tag Id) m) a }
  deriving (Eq, Eq1, Show, Show1, Functor, Foldable, Traversable, Applicative, Monad)
  
instance MonadTrans Enscope where
  lift = Enscope . lift . lift
  
instance Bound Enscope


instance Applicative Expr where
  pure = return
  (<*>) = ap

instance Monad Expr where
  return = Var
  
  String s        >>= _ = String s
  Number d        >>= _ = Number d
  Var a           >>= f = f a
  Undef           >>= _ = Undef
  Block en se     >>= f =
    Block (map (>>>= f) en) (M.map (>>>= f) se)
  e `At` x        >>= f = (e >>= f) `At` x
  e `Fix` x       >>= f = (e >>= f) `Fix` x
  e1 `Update` e2  >>= f = (e1 >>= f) `Update` (e2 >>= f)
  e1 `Concat` e2  >>= f = (e1 >>= f) `Concat` (e2 >>= f)
    
instance Eq1 Expr where
  liftEq eq (String sa)         (String sb)         = sa == sb
  liftEq eq (Number da)         (Number db)         = da == db
  liftEq eq (Var a)             (Var b)             = eq a b
  liftEq eq Undef               Undef               = True
  liftEq eq (Block ena sea)     (Block enb seb)     = 
    liftEq (liftEq eq) ena enb && liftEq (liftEq eq) sea seb
    
  liftEq eq (ea `At` xa)        (eb `At` xb)        =
    liftEq eq ea eb && xa == xb
    
  liftEq eq (ea `Fix` xa)       (eb `Fix` xb)       =
    liftEq eq ea eb && xa == xb
    
  liftEq eq (e1a `Update` e2a)  (e1b `Update` e2b)  =
    liftEq eq e1a e1b && liftEq eq e2a e2b
    
  liftEq eq (e1a `Concat` e2a)  (e1b `Concat` e2b)  =
    liftEq eq e1a e1b && liftEq eq e2a e2b
    
  liftEq _  _                   _                  = False
    
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
      
{-
instance Ord1 Expr where
  liftCompare _   (String sa)         (String sb)         = compare sa sb
  liftCompare _   (String _)          _                   = LT
  liftCompare _   _                   (String _)          = GT
  liftCompare _   (Number da)         (Number db)         = compare da db
  liftCompare _   (Number _)          _                   = LT
  liftCompare _   _                   (Number _)          = GT
  liftCompare cmp (Var a)             (Var b)             = cmp a b
  liftCompare _   (Var _)             _                   = LT
  liftCompare _   _                   (Var _)             = GT
  liftCompare _   Undef               Undef               = EQ
  liftCompare _   Undef               _                   = LT
  liftCompare _   _                   Undef               = GT
  liftCompare cmp (Block ia ena sea)  (Block ib enb seb)  =
    compare ia ib
    <> liftCompare (liftCompare cmp) ena enb
    <> liftCompare (liftCompare cmp) sea seb
    
  liftCompare _   (Block{})           _                   = LT
  liftCompare _   _                   (Block{})           = GT
  liftCompare cmp (ea `At` xa)        (eb `At` xb)        =
    liftCompare cmp ea eb <> compare xa xb
    
  liftCompare _   (At{})              _                   = LT
  liftCompare _   _                   (At{})              = GT
  liftCompare cmp (ea `Fix` xa)       (eb `Fix` xb)       =
    liftCompare cmp ea eb <> compare xa xb
    
  liftCompare _   (Fix{})             _                   = LT
  liftCompare _   _                   (Fix{})             = GT
  liftCompare cmp (e1a `Update` e2a)  (e1b `Update` e2b)  =
    liftCompare cmp e1a e1b <> liftCompare cmp e2a e2b
    
  liftCompare _   (Update{})          _                   = LT
  liftCompare _   _                   (Update{})          = GT
  liftCompare cmp (e1a `Concat` e2a)  (e1b `Concat` e2b)  =
    liftCompare cmp e1a e1b <> liftCompare cmp e2a e2b
    
--liftCompare _   (Concat{})          _                   = LT
--liftCompare _   _                   (Concat{})          = GT\
-}
  
    
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
mergeS (S a) (S b) = S <$> unionAWith mergeM a b
  
  
instance Ord a => Monoid (MRes (S a)) where
  mempty = pure emptyS
  
  a `mappend` b = join (liftA2 mergeS a b)
  

declS :: Path Id a -> S a
declS path = tree path (V Undef)
  

pathS :: Path Id a -> Expr a -> S a
pathS path = tree path . V


punS :: Path Id a -> S a
punS path = tree path emptyM


tree :: Path Id a -> M (Expr a) -> S a
tree = go
  where
    go (Pure a)                     = S . M.singleton a
    go (Free (path `Parser.At` x))  = go path . Tr . M.singleton x

  
pathM :: Path Id (Tag Id) -> a -> M a
pathM path = go path . V
  where
    go (Pure x)                     = Tr . M.singleton x
    go (Free (path `Parser.At` x))  = go path . Tr . M.singleton x
      

blockM :: Monoid m => (Expr a -> m) -> M (Expr a -> m) -> Expr a -> m
blockM rest = go1
  where
    --go1, go :: Monoid m => M (Expr a -> m) -> Expr a -> m
    go1 (V f)   e = f e 
    go1 (Tr m)  e = (rest . foldr (flip Fix) e) (M.keys m) <> go (Tr m) e
    
    go (V f)  e = f e
    go (Tr m) e = M.foldMapWithKey (flip go . At e) m
  

blockS :: S (Vis Id) -> Expr (Vis Id)
blockS (S m) =
  Block (M.elems en) se
  where
    (se, en) =
      M.foldrWithKey
        (\ k a (s, e) -> let
          aen = abstM (Enscope . abstract fenv . abstract fself) (return k) a
          ase = substitute k (lift Undef) aen
          in case k of
            Priv x -> (s, M.insert x aen e)
            Pub x -> (M.insert x ase s, e))
        (M.empty, M.empty)
        m
        
    blockM :: Expr (Vis Id) -> M (Expr (Vis Id)) -> Expr (Vis Id)
    blockM _ (V e) = e
    blockM p (Tr m) = Block [] (M.mapWithKey (lift . blockM . (At p))) `Concat` p' where
      p' = foldr (flip Fix) p (M.keys m)
        
    abstM ::
      (Expr (Vis Id) -> Enscope Expr (Vis Id))
        -> Expr (Vis Id)
        -> M (Expr (Vis Id))
        -> Enscope Expr (Vis Id)
    abstM f _ (V e) = f e
    abstM f p (Tr m) = (Enscope . Scope . Scope) 
      ((unscope . unscope . getEnscope . f) (Block [] m')
        `Concat` (unscope . unscope . getEnscope) (lift rem)) where
      rem = foldr (flip Fix) p (M.keys m)
      m' = M.mapWithKey  (abstM lift . (At p)) m
        
    -- Enscope Expr a ~ Scope Int (Scope (Tag Id) Expr) a
    -- unscope (Enscope Expr a) ~ Scope (Tag Id) Expr (Var Int (Scope (Tag Id) Expr a))
    -- unscope (unscope (Enscope Expr a)) ~ Expr (Var (Tag Id) (Expr (Var Int (Scope (Tag Id) Expr ))))
        
        
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
    
