{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies, PolyKinds, StandaloneDeriving, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Open(..), Comps(..)
  , Patt(..), match, abs, Decomp(..)
  , Eval(..), val
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
import My.Types.Prim (Prim(..), Eval(..))
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
data Repr k r a =
    Var a
  | Comps k r (Repr k r) a `At` k
    -- ^ Field access
  | Val (Comps k r (Repr k r) a) (Open k r (Repr k r) a)
  | Prim (Prim (Repr k r a))
    -- ^ Primitive values
--  deriving (Functor, Foldable, Traversable)

instance (Ord k, Show k) => Eval (Repr (Tag k) r a) where
  eval (c `At` k)   = fromMaybe (c `At` k) (call k (eval c))
  eval (Prim p)     = (Prim . eval) (p >>= \ e -> case eval e of
    Prim p -> p
    e      -> Embed e)
  eval e            = e


call :: (Ord k, Show k) => k -> Comps k r (Repr k r) a -> Maybe (Repr k r a)
call x = fromMaybe elime . go where
  elime = error ("eval: not a component: " ++ show x)

  go (Block b _)      = Just <$> M.lookup x b
  go (c `Fix` x')
    | x' == x         = Nothing
    | otherwise       = go c
  go (c1 `Concat` c2) = go c2 <|> fmap (<|> Just (c1 `At` x)) (go c1)
  go _                = Just Nothing
  
val :: (Ord k, Show k) => Open (Tag k) r (Repr (Tag k) r) a -> Repr (Tag k) r a
val o = e where
  e = Val (eval (App o emptyBlock e)) o
  emptyBlock = Block M.empty Nothing
  
-- c = fst e | c, c | { k => e } | c / k | o c e
-- eval (fst (c,o)) = eval c
-- eval ((d1,d2) c e) = eval (d1 c e), eval (d2 (eval (d1 c e)) e)
-- eval ((o / k) c _) = eval (o c (val o)) / k
-- eval ({ k => f } c e) = { k => f (c, e) }
data Comps k r m a =
    Comps (m a)
    -- ^ Get components of a value
  | Comps k r m a `Concat` Comps k r m a
  | Block (M.Map k (m a)) (Maybe (m r -> m a))
    -- ^ Set of public components
  | Comps k r m a `Fix` k
    -- ^ Fix a component
  | App (Open k r m a) (Comps k r m a) (m a)
    -- ^ Bind 'self' and 'super' values
  deriving (Functor) --, Foldable, Traversable)
  
instance Ord k => Bound (Comps k r) where
  Comps e        >>>= f = Comps (e >>= f)
  c1 `Concat` c2 >>>= f = (c1 >>>= f) `Concat` (c2 >>>= f)
  c `Fix` x      >>>= f = (c >>>= f) `Fix` x
  Block b k      >>>= f = Block (M.map (>>= f) b) (fmap (>=> f) k)
  App o c e      >>>= f = App (o >>>= f) (c >>>= f) (e >>= f)
  
instance (Ord k, Show k) => Eval (Comps (Tag k) r (Repr (Tag k) r) a) where
  eval (Comps e)        = go (eval e) where
    go (Val c _) = c
    go (Prim p)  = go (val (primOpen p))
    go e         = Comps e
  eval (c1 `Concat` c2) = eval c1 `Concat` eval c2
  eval (c `Fix` k)      = eval c `Fix` k
  eval (App o su se)    = go o where
    go (Open e)        = case eval e of
      Val _ o        -> go o
      Prim p         -> go (primOpen p)
      e              -> App (Open e) su se
    go (Lift c)         = c
    go (d1 `Update` d2) = su' `Concat` eval (App d2 su' se) where
      su' = go d1
    go (Abs pas en b k)   = Block (M.map f b) (fmap (f .) k) where
      en' = fmap f en
      pas' = foldMap (\ (p, a) -> match p (f a)) pas
      f = eval . instantiate (ref (At su) (pas' !!) (en' !!) se)
  eval c                 = c

-- o =: snd e | o, o | { k => f }
data Open k r m a =
    Open (m a)
  | Lift (Comps k r m a)
  | Open k r m a `Update` Open k r m a
    -- ^ Chain definitions
  | Abs
      [(Patt k, Scope (Ref k) m a)]
      -- ^ Set of destructing patterns
      [Scope (Ref k) m a]
      -- ^ local definitions
      (M.Map k (Scope (Ref k) m a)) 
      -- ^ public definitions
      (Maybe (m r -> Scope (Ref k) m a))
      -- ^ scope browser
  deriving (Functor) --, Foldable, Traversable)
  
instance Ord k => Bound (Open k r) where
  Open e         >>>= f = Open (e >>= f)
  Lift c         >>>= f = Lift (c >>>= f)
  d1 `Update` d2 >>>= f = (d1 >>>= f) `Update` (d2 >>>= f)
  Abs pas en b k >>>= f = Abs
    (fmap (fmap (>>>= f)) pas)
    (fmap (>>>= f) en)
    (fmap (>>>= f) b)
    (fmap (\ k r -> k r >>>= f) k)
  

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
    

match :: (Ord k, Show k) => Patt (Tag k) -> Repr (Tag k) r a -> [Repr (Tag k) r a]
match = go where
  go Skip                _ = mempty
  go Bind                e = pure e
  go (p `Rest` Decomp m) e = maybe mempty (go p) mb <> xs where
    (xs, mb) = kf (M.map (\ f -> iter kf (f <&> (\ p e -> (go p e, Nothing)))) m) e
    
    kf
      :: (Ord k, Show k, Applicative f)
      => M.Map (Tag k) (Repr (Tag k) r a -> f (Maybe (Repr (Tag k) r a)))
      -> Repr (Tag k) r a ->  f (Maybe (Repr (Tag k) r a))
    kf m e = traverseMaybeWithKey
      (\ i k -> k (eval (Comps e `At` i)))
      m <&> (\ m' -> let c = hide (Comps e) (M.keys m) `Concat` Block m' Nothing in
        Just (Val c (Lift c)))
        
      
    -- | Folds over a value to find keys to restrict for an expression.
    --
    -- Can be used as function to construct an expression of the 'left-over' components
    -- assigned to nested ungroup patterns.
    hide :: Foldable f => Comps (Tag k) r m a -> f (Tag k) -> Comps (Tag k) r m a
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


instance (Ord k, Show k) => Functor (Repr (Tag k) r) where
  fmap f (Var a) = Var (f a)
  fmap f (c `At` k) = fmap f c `At` k
  fmap f (Val _ o) = val (fmap f o)
  fmap f (Prim p) = Prim (fmap (fmap f) p)
  
instance (Ord k, Show k) => Applicative (Repr (Tag k) r) where
  pure = Var
  (<*>) = ap
  
instance (Ord k, Show k) => Monad (Repr (Tag k) r) where
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

instance (Ord k, Show k, Eq a) => Eq (Repr (Tag k) r a) where
  (==) = (==#)
  
instance (Ord k, Show k) => Eq1 (Repr (Tag k) r) where
  Var a       ==# Var b        = a == b
  (ca `At` x) ==# (cb `At` x') = ca ==# cb && x == x'
  Val _ oa    ==# Val _ ob     = oa ==# ob
  Prim pa     ==# Prim pb      = pa ==# pb
  _           ==# _            = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Comps k r m) where
  Comps ea           ==# Comps eb           = ea ==# eb
  (c1a `Concat` c2a) ==# (c1b `Concat` c2b) = c1a ==# c1b && c2a ==# c2b
  Block ba _         ==# Block bb _         = liftmap ba == liftmap bb where
    liftmap :: M.Map k (m a) -> M.Map k (Lift1 m a)
    liftmap = coerce
  (ca `Fix` x)       ==# (cb `Fix` x')      = ca ==# cb && x == x'
  App da ea ca       ==# App db eb cb       = da ==# db && ea ==# eb && ca ==# cb
  _                  ==# _                  = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Open k r m) where
  Open ea            ==# Open eb            = ea ==# eb
  Lift ca            ==# Lift cb            = ca ==# cb
  (d1a `Update` d2a) ==# (d1b `Update` d2b) = d1a ==# d1b && d2a ==# d2b
  Abs pas ena ba _   ==# Abs pbs enb bb _   = pas ==# pbs && ena ==# enb && ba == bb
  _                  ==# _                  = False
    
    
instance (Ord k, Show k, Show a) => Show (Repr (Tag k) r a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr (Tag k) r) where
  showsPrec1 i e = case e of
    Var a      -> showsUnaryWith showsPrec "Var" i a
    c `At` x   -> showsBinaryWith showsPrec1 showsPrec "At" i c x
    Val _ b    -> showsUnaryWith showsPrec1 "val" i b
    Prim p     -> showsUnaryWith showsPrec1 "Prim" i p
      
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Comps k r m) where
  showsPrec1 i e = case e of
    Comps e        -> showsUnaryWith showsPrec1 "Closed" i e
    c1 `Concat` c2 -> showsBinaryWith showsPrec1 showsPrec1 "Concat" i c1 c2
    Block b _      -> showsUnaryWith showsPrec "Block" i (liftmap b) where
      liftmap = coerce :: M.Map k (m a) -> M.Map k (Lift1 m a)
    c `Fix` x      -> showsBinaryWith showsPrec1 showsPrec "Fix" i c x
    App o e c      -> showsTrinaryWith showsPrec1 showsPrec1 showsPrec1 "App" i o e c
  
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Open k r m) where
  showsPrec1 i e = case e of
    Open e         -> showsUnaryWith showsPrec1 "Open" i e
    Lift c         -> showsUnaryWith showsPrec1 "Lift" i c
    d1 `Update` d2 -> showsBinaryWith showsPrec1 showsPrec1 "Concat" i d1 d2
    Abs pas en b _ -> showsTrinaryWith showsPrec showsPrec showsPrec "Abs" i pas en b
      
instance S.Local a => S.Local (Nec a) where local_ i = Req (S.local_ i)
instance S.Self a => S.Self (Nec a) where self_ i = Req (S.self_ i)

instance S.Self a => S.Self (Repr k r a) where self_ i = Var (S.self_ i)
instance S.Local a => S.Local (Repr k r a) where local_ i = Var (S.local_ i)
  
instance S.Field (Repr (Tag k) r a) where
  type Compound (Repr (Tag k) r a) = Repr (Tag k) r a
  e #. i = Comps e `At` Key i

instance Num (Repr k r a) where
  fromInteger = Prim . fromInteger
  a + b = Prim (Embed a + Embed b)
  a - b = Prim (Embed a - Embed b)
  a * b = Prim (Embed a * Embed b)
  abs = Prim . abs . Embed
  signum = Prim . signum . Embed
  negate = Prim . negate . Embed
  
instance Fractional (Repr k r a) where
  fromRational = Prim . fromRational
  a / b = Prim (Embed a / Embed b)
  
instance IsString (Repr k r a) where
  fromString = Prim . fromString

instance S.Lit (Repr k r a) where
  unop_ op = Prim . Unop op . Embed
  binop_ op a b = Prim (Binop op (Embed a) (Embed b))

    
instance Show (IOPrimTag a) where
  showsPrec i _ = error "show: IOPrimTag"

-- | Built-in representations for primitive types
primOpen :: (Ord k, Show k) => Prim p -> Open (Tag k) r (Repr (Tag k) r) a
primOpen (Number d)  = error "eval: number #unimplemented"
primOpen (Text s)    = error "eval: text #unimplemented"
primOpen (Bool b)    = boolOpen b
primOpen (IOError e) = error "eval: ioerror #unimplemented"
      
-- | Bool
boolOpen :: (Ord k, Show k) => Bool -> Open (Tag k) r (Repr (Tag k) r) a
boolOpen b = Abs [] []
  (M.singleton
    (Key "match")
    (Scope (Comps (Var (B Self)) `At` Key (if b then "ifTrue" else "ifFalse"))))
  Nothing
  
  
