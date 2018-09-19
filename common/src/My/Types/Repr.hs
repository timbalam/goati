{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies, PolyKinds, StandaloneDeriving, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Open(..), Comps(..)
  , Patt(..), match, Decomp(..)
  , Browse(..), Assoc(..), IsAssoc(..)
  , eval, val, appAbs
  , Ref(..), ref
  , Prim(..)
  , IOPrimTag(..)
  , Tag(..)
  , Nec(..), nec
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  )
  where
  

import qualified My.Types.Syntax.Class as S
import My.Types.Prim (Prim(..), evalPrim)
--import qualified My.Types.Parser as P
import My.Util (showsUnaryWith, showsBinaryWith, showsTrinaryWith, (<&>), traverseMaybeWithKey)
import Control.Applicative (liftA2, (<|>))
import Control.Monad (ap, (>=>))
import Control.Monad.Trans (lift)
import Control.Monad.Free (Free(..), iter)
import Control.Monad.State (state, evalState)
import Control.Exception (IOException)
import Data.Coerce (coerce)
--import Data.Functor.Classes
import Prelude.Extras
import Data.IORef (IORef)
import qualified Data.Map as M
--import qualified Data.Map.Merge.Lazy as M
import Data.Maybe (fromMaybe)
--import qualified Data.Set as S
import Data.Semigroup (Semigroup(..))
import Data.String (IsString(..))
import qualified Data.Text as T
import Data.Traversable (foldMapDefault, fmapDefault)
import System.IO (Handle, IOMode)
import Bound
  

-- | Runtime value representation 
-- e := a | c k | c, o | ...
-- eval ({ k => e} k) = e
-- eval ((c / k) k) = !
-- eval ({} k) = !
data Repr f k a =
    Var a
  | Comps f k (Repr f k) a `At` k
    -- ^ Field access
  | Val (Comps f k (Repr f k) a) (Open f k (Repr f k) a)
  | Prim (Prim (Repr f k a))
    -- ^ Primitive values
--  deriving (Functor, Foldable, Traversable)

eval
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => Repr s (Tag k) a -> Repr s (Tag k) a
eval (c `At` k)   = fromMaybe (c `At` k) (call k (evalComps c))
eval (Prim p)     = (Prim . evalPrim) (p >>= \ e -> case eval e of
  Prim p -> p
  e      -> Embed e)
eval e            = e


call :: (Ord k, Show k, IsAssoc s) => k -> Comps s k (Repr s k) a -> Maybe (Repr s k a)
call x = fromMaybe elime . go where
  elime = error ("eval: not a component: " ++ show x)

  go (Block b)      = Just <$> getAssoc x b
  go (c `Fix` x')
    | x' == x         = Nothing
    | otherwise       = go c
  go (c1 `Concat` c2) = go c2 <|> fmap (<|> Just (c1 `At` x)) (go c1)
  go _                = Just Nothing

  
val
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => Open s (Tag k) (Repr s (Tag k)) a -> Repr s (Tag k) a
val o = e where
  e = Val (evalComps (App o emptyBlock e)) o
  emptyBlock = Block (fromMap M.empty)
  
  
-- c = fst e | c, c | { k => e } | c / k | o c e
-- eval (fst (c,o)) = eval c
-- eval ((d1,d2) c e) = eval (d1 c e), eval (d2 (eval (d1 c e)) e)
-- eval ((o / k) c _) = eval (o c (val o)) / k
-- eval ({ k => f } c e) = { k => f (c, e) }
data Comps f k m a =
    Comps (m a)
    -- ^ Get components of a value
  | Comps f k m a `Concat` Comps f k m a
  | Block (f k (m a))
    -- ^ Set of public components
  | Comps f k m a `Fix` k
    -- ^ Fix a component
  | App (Open f k m a) (Comps f k m a) (m a)
    -- ^ Bind 'self' and 'super' values
  deriving (Functor) --, Foldable, Traversable)
  
instance (Ord k, Functor (f k)) => Bound (Comps f k) where
  Comps e        >>>= f = Comps (e >>= f)
  c1 `Concat` c2 >>>= f = (c1 >>>= f) `Concat` (c2 >>>= f)
  c `Fix` x      >>>= f = (c >>>= f) `Fix` x
  Block b        >>>= f = Block (fmap (>>= f) b)
  App o c e      >>>= f = App (o >>>= f) (c >>>= f) (e >>= f)
  
evalComps
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => Comps s (Tag k) (Repr s (Tag k)) a
  -> Comps s (Tag k) (Repr s (Tag k)) a
evalComps (Comps e)        = go (eval e) where
  go (Val c _) = c
  go (Prim p)  = go (val (primOpen p))
  go e         = Comps e
evalComps (c1 `Concat` c2) = evalComps c1 `Concat` evalComps c2
evalComps (c `Fix` k)      = evalComps c `Fix` k
evalComps (App o su se)    = go o where
  go (Open e)        = case eval e of
    Val _ o        -> go o
    Prim p         -> go (primOpen p)
    e              -> App (Open e) su se
  go (Lift c)         = c
  go (d1 `Update` d2) = su' `Concat` evalComps (App d2 su' se) where
    su' = go d1
  go (Abs pas en b)   = Block (appAbs su se pas en b)
evalComps c                 = c


appAbs
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => Comps s (Tag k) (Repr s (Tag k)) a
  -> Repr s (Tag k) a 
  -> [(Patt (Tag k), Scope (Ref (Tag k)) (Repr s (Tag k)) a)]
  -> [Scope (Ref (Tag k)) (Repr s (Tag k)) a]
  -> s (Tag k) (Scope (Ref (Tag k)) (Repr s (Tag k)) a)
  -> s (Tag k) (Repr s (Tag k) a)
appAbs su se pas en b = fmap f b where
  en' = fmap f en
  pas' = foldMap (\ (p, a) -> match p (f a)) pas
  f = eval . instantiate (ref (At su) (pas' !!) (en' !!) se)

  
-- o =: snd e | o, o | { k => f }
data Open f k m a =
    Open (m a)
  | Lift (Comps f k m a)
  | Open f k m a `Update` Open f k m a
    -- ^ Chain definitions
  | Abs
      [(Patt k, Scope (Ref k) m a)]
      -- ^ Set of destructing patterns
      [Scope (Ref k) m a]
      -- ^ local definitions
      (f k (Scope (Ref k) m a))
      -- ^ public definitions
  deriving (Functor) --, Foldable, Traversable)
  
instance (Ord k, Functor (f k)) => Bound (Open f k) where
  Open e         >>>= f = Open (e >>= f)
  Lift c         >>>= f = Lift (c >>>= f)
  d1 `Update` d2 >>>= f = (d1 >>>= f) `Update` (d2 >>>= f)
  Abs pas en b   >>>= f = Abs
    (fmap (fmap (>>>= f)) pas)
    (fmap (>>>= f) en)
    (fmap (>>>= f) b)
  

-- p =: _ | a | p { k => p }
data Patt k =
    Skip
    -- ^ skip matched part
  | Bind
    -- ^ bind match part
  | Patt k `Rest` Decomp k (Patt k)
    -- ^ decompose subset of fields matched part, with possibility to match remainder
  deriving (Eq, Show)
  
newtype Decomp k a = Decomp (M.Map k (Free (M.Map k) a))
  deriving (Eq, Show)
    

match
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => Patt (Tag k) -> Repr s (Tag k) a -> [Repr s (Tag k) a]
match = go where
  --go
  --  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  --  => Patt (Tag k) -> Repr s (Tag k) a -> [Repr s (Tag k) a]
  go Skip                _ = mempty
  go Bind                e = pure e
  go (p `Rest` Decomp m) e = maybe mempty (go p) mb <> xs where
    (xs, mb) = kf (M.map (\ f -> iter kf (f <&> (\ p e -> (go p e, Nothing)))) m) e
    
  kf
    :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s, Applicative f)
    => M.Map (Tag k) (Repr s (Tag k) a -> f (Maybe (Repr s (Tag k) a)))
    -> Repr s (Tag k) a ->  f (Maybe (Repr s (Tag k) a))
  kf m e = traverseMaybeWithKey
    (\ i k -> k (eval (Comps e `At` i)))
    m <&> (\ m' -> let c = hide (Comps e) (M.keys m) `Concat` Block (fromMap m') in
      Just (Val c (Lift c)))
      
    
  -- | Folds over a value to find keys to restrict for an expression.
  --
  -- Can be used as function to construct an expression of the 'left-over' components
  -- assigned to nested ungroup patterns.
  hide :: Foldable f => Comps s (Tag k) m a -> f (Tag k) -> Comps s (Tag k) m a
  hide = foldl Fix
  
  
-- | Marker type for self- and env- references
data Ref k = Super k | Match Int | Env Int | Self deriving (Eq, Show)

ref :: (k -> a) -> (Int -> a) -> (Int -> a) -> a -> Ref k -> a
ref f _ _ _ (Super k) = f k
ref _ g _ _ (Match i) = g i 
ref _ _ h _ (Env i)   = h i
ref _ _ _ a Self      = a
  
  
-- | Primitive my language field tags
data IOPrimTag a =
    OpenFile IOMode
  | HGetLine Handle
  | HGetContents Handle
  | HPutStr Handle
  | NewMut
  | GetMut (IORef a)
  | SetMut (IORef a)
  deriving Eq
  
  
-- | Expression key type
data Tag k =
    Key S.Ident
  | Symbol k
  deriving (Eq, Show)
  
-- Manually implemented to guarantee Key is monotonic with respect to underlying ordering (relied upon in My.Syntax.Expr class implementations)
instance Ord k => Ord (Tag k) where
  compare (Key a)     (Key b)     = compare a b
  compare (Key _)     _           = GT
  compare _           (Key _ )    = LT
  compare (Symbol a)  (Symbol b)  = compare a b
  
  
data Nec a = Req a | Opt a
  deriving (Eq, Show)

nec :: (a -> b) -> (a -> b) -> Nec a -> b
nec f _ (Req a) = f a
nec _ g (Opt a) = g a


instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s) => Functor (Repr s (Tag k)) where
  fmap f (Var a) = Var (f a)
  fmap f (c `At` k) = fmap f c `At` k
  fmap f (Val _ o) = val (fmap f o)
  fmap f (Prim p) = Prim (fmap (fmap f) p)
  
instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s) => Applicative (Repr s (Tag k)) where
  pure = Var
  (<*>) = ap
  
instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s) => Monad (Repr s (Tag k)) where
  return = pure
  
  Var a      >>= f = f a
  c `At` x   >>= f = (c >>>= f) `At` x
  Val _ o    >>= f = val (o >>>= f)
  Prim p     >>= f = Prim (fmap (>>= f) p)
  
{-
instance (Ord k, Show k, Eq a) => Eq (Repr (Tag k) r a) where
  (==) = eq1
  
instance (Ord k, Show k) => Eq1 (Repr (Tag k) r) where
  liftEq eq (Var a)       (Var b)       = eq a b
  liftEq eq (ca `At` x)   (cb `At` x')  = liftEq eq ca cb && x == x'
  liftEq eq (Val _ oa)    (Val _ ob)    = liftEq eq oa ob
  liftEq eq (Prim pa)     (Prim pb)     = liftEq (liftEq eq) pa pb
  liftEq _  _             _             = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Comps k r m) where
  liftEq eq (Comps ea)         (Comps eb)         = liftEq eq ea eb
  liftEq eq (c1a `Concat` c2a) (c1b `Concat` c2b) = liftEq eq c1a c1b && liftEq eq c2a c2b
  liftEq eq (Block ba _)       (Block bb _)       = liftEq (liftEq eq) ba bb
  liftEq eq (ca `Fix` x)       (cb `Fix` x')      = liftEq eq ca cb && x == x'
  liftEq eq (App da ea ca)     (App db eb cb)     = liftEq eq da db &&
    liftEq eq ea eb && liftEq eq ca cb
  liftEq _  _                  _                  = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Open k r m) where
  liftEq eq (Open ea)          (Open eb)          = liftEq eq ea eb
  liftEq eq (Lift ca)          (Lift cb)          = liftEq eq ca cb
  liftEq eq (d1a `Update` d2a) (d1b `Update` d2b) = liftEq eq d1a d1b && liftEq eq d2a d2b
  liftEq eq (Abs pas ena ba _) (Abs pbs enb bb _) = liftEq (liftEq (liftEq eq)) pas pbs &&
    liftEq (liftEq eq) ena enb && liftEq (liftEq eq) ba bb
  liftEq _  _                  _                  = False
    
    
instance (Ord k, Show k, Show a) => Show (Repr (Tag k) r a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr (Tag k) r) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Repr (Tag k) r a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a      -> showsUnaryWith f "Var" i a
    c `At` x   -> showsBinaryWith f' showsPrec "At" i c x
    Val _ b    -> showsUnaryWith f' "val" i b
    Prim p     -> showsUnaryWith f'' "Prim" i p
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Comps k r m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Comps k r m a -> ShowS
  liftShowsPrec f g i e = case e of
    Comps e        -> showsUnaryWith f' "Closed" i e
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    Block b _      -> showsUnaryWith f'' "Block" i b
    c `Fix` x      -> showsBinaryWith f' showsPrec "Fix" i c x
    App o e c      -> showsTrinaryWith f' f' f' "App" i o e c
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
  
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Open k r m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k r m a -> ShowS
  liftShowsPrec f g i e = case e of
    Open e         -> showsUnaryWith f' "Open" i e
    Lift c         -> showsUnaryWith f' "Lift" i c
    d1 `Update` d2 -> showsBinaryWith f' f' "Concat" i d1 d2
    Abs pas en b _ -> showsTrinaryWith f''' f'' f'' "Abs" i pas en b
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      g'' = liftShowList f' g'
      f''' = liftShowsPrec f'' g''
-}

instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s, Eq1 (s (Tag k)), Eq a)
  => Eq (Repr s (Tag k) a) where
  (==) = (==#)
  
instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s, Eq1 (s (Tag k)))
  => Eq1 (Repr s (Tag k)) where
  Var a       ==# Var b        = a == b
  (ca `At` x) ==# (cb `At` x') = ca ==# cb && x == x'
  Val _ oa    ==# Val _ ob     = oa ==# ob
  Prim pa     ==# Prim pb      = pa ==# pb
  _           ==# _            = False
  
instance (Ord k, Eq1 m, Monad m, Functor (s k), Eq1 (s k)) => Eq1 (Comps s k m) where
  Comps ea           ==# Comps eb           = ea ==# eb
  (c1a `Concat` c2a) ==# (c1b `Concat` c2b) = c1a ==# c1b && c2a ==# c2b
  Block ba           ==# Block bb           = fmap Lift1 ba ==# fmap Lift1 bb
  (ca `Fix` x)       ==# (cb `Fix` x')      = ca ==# cb && x == x'
  App da ea ca       ==# App db eb cb       = da ==# db && ea ==# eb && ca ==# cb
  _                  ==# _                  = False
  
instance (Ord k, Eq1 m, Monad m, Functor (s k), Eq1 (s k)) => Eq1 (Open s k m) where
  Open ea            ==# Open eb            = ea ==# eb
  Lift ca            ==# Lift cb            = ca ==# cb
  (d1a `Update` d2a) ==# (d1b `Update` d2b) = d1a ==# d1b && d2a ==# d2b
  Abs pas ena ba     ==# Abs pbs enb bb     = pas ==# pbs && ena ==# enb && ba ==# bb
  _                  ==# _                  = False
    
    
instance (Ord k, Show k, Functor (s (Tag k)), Show1 (s (Tag k)), IsAssoc s, Show a)
  => Show (Repr s (Tag k) a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k, Functor (s (Tag k)), Show1 (s (Tag k)), IsAssoc s)
  => Show1 (Repr s (Tag k)) where
  showsPrec1 i e = case e of
    Var a      -> showsUnaryWith showsPrec "Var" i a
    c `At` x   -> showsBinaryWith showsPrec1 showsPrec "At" i c x
    Val _ b    -> showsUnaryWith showsPrec1 "val" i b
    Prim p     -> showsUnaryWith showsPrec1 "Prim" i p
      
instance (Ord k, Show k, Functor (s k), Show1 (s k), Show1 m, Monad m)
  => Show1 (Comps s k m) where
  showsPrec1 i e = case e of
    Comps e        -> showsUnaryWith showsPrec1 "Closed" i e
    c1 `Concat` c2 -> showsBinaryWith showsPrec1 showsPrec1 "Concat" i c1 c2
    Block b        -> showsUnaryWith showsPrec1 "Block" i (fmap Lift1 b)
    c `Fix` x      -> showsBinaryWith showsPrec1 showsPrec "Fix" i c x
    App o e c      -> showsTrinaryWith showsPrec1 showsPrec1 showsPrec1 "App" i o e c
  
instance (Ord k, Show k, Functor (s k), Show1 (s k), Show1 m, Monad m)
  => Show1 (Open s k m) where
  showsPrec1 i e = case e of
    Open e         -> showsUnaryWith showsPrec1 "Open" i e
    Lift c         -> showsUnaryWith showsPrec1 "Lift" i c
    d1 `Update` d2 -> showsBinaryWith showsPrec1 showsPrec1 "Concat" i d1 d2
    Abs pas en b   -> showsTrinaryWith showsPrec showsPrec showsPrec1 "Abs" i pas en b
      
instance S.Local a => S.Local (Nec a) where local_ i = Req (S.local_ i)
instance S.Self a => S.Self (Nec a) where self_ i = Req (S.self_ i)

instance S.Self a => S.Self (Repr s k a) where self_ i = Var (S.self_ i)
instance S.Local a => S.Local (Repr s k a) where local_ i = Var (S.local_ i)
  
instance S.Field (Repr s (Tag k) a) where
  type Compound (Repr s (Tag k) a) = Repr s (Tag k) a
  e #. i = Comps e `At` Key i

instance Num (Repr s k a) where
  fromInteger = Prim . fromInteger
  a + b = Prim (Embed a + Embed b)
  a - b = Prim (Embed a - Embed b)
  a * b = Prim (Embed a * Embed b)
  abs = Prim . abs . Embed
  signum = Prim . signum . Embed
  negate = Prim . negate . Embed
  
instance Fractional (Repr s k a) where
  fromRational = Prim . fromRational
  a / b = Prim (Embed a / Embed b)
  
instance IsString (Repr s k a) where
  fromString = Prim . fromString

instance S.Lit (Repr s k a) where
  unop_ op = Prim . Unop op . Embed
  binop_ op a b = Prim (Binop op (Embed a) (Embed b))

    
instance Show (IOPrimTag a) where
  showsPrec i _ = error "show: IOPrimTag"
  

-- | Associative arrays
class IsAssoc f where
  getAssoc :: Ord k => k -> f k a -> Maybe a
  fromMap :: M.Map k a -> f k a
  
-- | 'Browsable' associations implementation
data Browse r k a = Browse (Maybe (Repr (Browse r) k r -> a)) (M.Map k a)
  deriving Functor
  
instance (Eq k, Eq a) => Eq (Browse r k a) where
  (==) = (==#)
  
instance Eq k => Eq1 (Browse r k) where
  Browse _ ma ==# Browse _ mb = ma == mb
  
instance (Show k, Show a) => Show (Browse r k a) where
  showsPrec = showsPrec1
  
instance Show k => Show1 (Browse r k) where
  showsPrec1 i (Browse _ m) = showsUnaryWith showsPrec "fromMap" i m
  
instance IsAssoc (Browse r) where
  getAssoc k (Browse _ m) = M.lookup k m
  fromMap m = Browse Nothing m
  
-- | Standard association
newtype Assoc k a = Assoc (M.Map k a)
  deriving Functor
  
instance (Eq k, Eq a) => Eq (Assoc k a) where
  (==) = (==#)
  
instance Eq k => Eq1 (Assoc k) where
  Assoc ma ==# Assoc mb = ma == mb
  
instance (Show k, Show a) => Show (Assoc k a) where
  showsPrec = showsPrec1
  
instance Show k => Show1 (Assoc k) where
  showsPrec1 i (Assoc m) = showsUnaryWith showsPrec "Assoc" i m
  
instance IsAssoc Assoc where 
  getAssoc k (Assoc m) = M.lookup k m
  fromMap = Assoc
  

-- | Built-in representations for primitive types
primOpen :: (Ord k, Show k, IsAssoc s) => Prim p -> Open s (Tag k) (Repr s (Tag k)) a
primOpen (Number d)  = error "eval: number #unimplemented"
primOpen (Text s)    = error "eval: text #unimplemented"
primOpen (Bool b)    = boolOpen b
primOpen (IOError e) = error "eval: ioerror #unimplemented"
      
-- | Bool
boolOpen :: (Ord k, Show k, IsAssoc s) => Bool -> Open s (Tag k) (Repr s (Tag k)) a
boolOpen b = Abs [] []
  (fromMap (M.singleton
    (Key "match")
    (Scope (Comps (Var (B Self)) `At` Key (if b then "ifTrue" else "ifFalse")))))
  
  
