{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies, PolyKinds, StandaloneDeriving, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}

-- | Module of my language core data type representation
module My.Types.Repr
  ( Repr(..), Open(..), Comps(..)
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
import My.Types.Syntax.Class
import My.Types.Prim (Prim(..), Eval(..))
import My.Util (showsTrinaryWith)
import Control.Applicative (liftA2, (<|>))
--import qualified Control.Category as C (Category(..))
import Control.Monad (ap)
import Control.Monad.Trans
import Control.Monad.Trans.Identity (IdentityT(..))
import Control.Exception (IOException)
import Data.Functor.Classes
import Data.IORef (IORef)
import qualified Data.Map as M
import qualified Data.Map.Merge.Lazy as M
import Data.Maybe (fromMaybe)
--import qualified Data.Set as S
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
data Repr k a = 
    Var a
  | Comps k (Repr k) a `At` k
    -- ^ Field access
  | Val (Comps k (Repr k) a) (Open k (Repr k) a)
  | Let [Scope Int (Repr k) a] (Scope Int (Repr k) a)
    -- ^ Local recursive definitions
  | Prim (Prim (Repr k a))
    -- ^ Primitive values
  deriving (Functor, Foldable, Traversable)

instance (Ord k, Show k) => Eval (Repr (Tag k) a) where
  eval (c `At` k) = fromMaybe (c `At` k) (call k (eval c))
  eval (Let en s) = f s where
    f = eval . instantiate (en' !!)
    en' = map f en
  eval (Prim p)   = (Prim . eval) (p >>= \ e -> case eval e of
    Prim p -> p
    e      -> Embed e)
  eval e          = e

call :: (Ord k, Show k) => k -> Comps k (Repr k) a -> Maybe (Repr k a)
call x = fromMaybe elime . go where
  elime = error ("eval: not a component: " ++ show x)

  go (Block b)        = Just <$> M.lookup x b
  go (c `Hide` x')
    | x' == x         = Nothing
    | otherwise       = go c
  go (c1 `Concat` c2) = go c2 <|> fmap (<|> Just (c1 `At` x)) (go c1)
  go _                = Just Nothing
  
val :: (Ord k, Show k) => Open (Tag k) (Repr (Tag k)) a -> Repr (Tag k) a
val o = e where
  e = Val (eval (App o emptyBlock e)) o
  emptyBlock = Block M.empty
  
-- c = fst e | c, c | { k => e } | c / k | o c e
-- eval (fst (c,o)) = eval c
-- eval ((d1,d2) c e) = eval (d1 c e), eval (d2 (eval (d1 c e)) e)
-- eval ((o / k) c _) = eval (o c (val o)) / k
-- eval ({ k => f } c e) = { k => f (c, e) }
data Comps k m a =
    Comps (m a)
    -- ^ Get components of a value
  | Comps k m a `Concat` Comps k m a
  | Block (M.Map k (m a))
    -- ^ Set of public components
  | Comps k m a `Hide` k
    -- ^ Hide a component
  | App (Open k m a) (Comps k m a) (m a)
    -- ^ Bind 'self' and 'super' values
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Show k) => Eval (Comps (Tag k) (Repr (Tag k)) a) where
  eval (Comps e)        = go (eval e) where
    go (Val c _) = c
    go (Prim p)  = go (val (primOpen p))
    go e         = Comps e
  eval (c1 `Concat` c2) = eval c1 `Concat` eval c2
  eval (c `Hide` k)     = eval c `Hide` k
  eval (App o su se)    = go o where
    go (Open e)        = case eval e of
      Val _ o -> go o
      Prim p  -> go (primOpen p)
      e       -> App (Open e) su se
    go (d1 `Update` d2) = su' `Concat` eval (App d2 su' se) where
      su' = go d1
    go (o `Fix` x)      = eval (App o su (val o)) `Hide` x
    go (Abs b)          = Block (M.map f b) where
      f = eval . instantiate (ref (At su) se)
  eval c                 = c
  
instance Ord k => Bound (Comps k) where
  Comps e        >>>= f = Comps (e >>= f)
  c1 `Concat` c2 >>>= f = (c1 >>>= f) `Concat` (c2 >>>= f)
  c `Hide` x     >>>= f = (c >>>= f) `Hide` x
  Block b        >>>= f = Block (M.map (>>= f) b)
  App o c e      >>>= f = App (o >>>= f) (c >>>= f) (e >>= f)

-- o = snd e | o, o | { k => f } | o / k
data Open k m a =
    Open (m a)
  | Open k m a `Update` Open k m a
    -- ^ Chain definitions
  | Abs (M.Map k (Scope (Ref k) m a))
    -- ^ Set of public definitions
  | Open k m a `Fix` k
    -- ^ Fix a component
  deriving (Functor, Foldable, Traversable)
  
instance Ord k => Bound (Open k) where
  Open e         >>>= f = Open (e >>= f)
  d1 `Update` d2 >>>= f = (d1 >>>= f) `Update` (d2 >>>= f)
  Abs b          >>>= f = Abs (M.map (>>>= f) b)
  o `Fix` x      >>>= f = (o >>>= f) `Fix` x
  
  
-- | Marker type for self- and super- references
data Ref k = Super k | Self deriving (Eq, Show)

ref :: (k -> a) -> a -> Ref k -> a
ref f _ (Super k) = f k
ref _ a Self      = a
  
  
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

nec :: (a -> b) -> (a -> b) -> Nec a -> b
nec f g (Req a) = f a
nec f g (Opt a) = g a
  
  
instance Ord k => Applicative (Repr k) where
  pure = Var
  (<*>) = ap
  
instance Ord k => Monad (Repr k) where
  return = pure
  
  Var a     >>= f = f a
  c `At` x  >>= f = (c >>>= f) `At` x
  Val c o   >>= f = Val (c >>>= f) (o >>>= f)
  Let en s  >>= f = Let (map (>>>= f) en) (s >>>= f)
  Prim p    >>= f = Prim (fmap (>>= f) p)
  

instance (Ord k, Eq a) => Eq (Repr k a) where
  (==) = eq1
  
instance Ord k => Eq1 (Repr k) where
  liftEq eq (Var a)      (Var b)       = eq a b
  liftEq eq (ca `At` x)  (cb `At` x')  = liftEq eq ca cb && x == x'
  liftEq eq (Val _ oa)   (Val _ ob)    = liftEq eq oa ob
  liftEq eq (Let ena sa) (Let enb sb)  = liftEq (liftEq eq) ena enb && liftEq eq sa sb
  liftEq _  _            _             = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Comps k m) where
  liftEq eq (Comps ea)         (Comps eb)         = liftEq eq ea eb
  liftEq eq (c1a `Concat` c2a) (c1b `Concat` c2b) = liftEq eq c1a c1b && liftEq eq c2a c2b
  liftEq eq (Block ba)         (Block bb)         = liftEq (liftEq eq) ba bb
  liftEq eq (ca `Hide` x)      (cb `Hide` x')     = liftEq eq ca cb && x == x'
  liftEq eq (App da ea ca)     (App db eb cb)     = liftEq eq da db &&
    liftEq eq ea eb && liftEq eq ca cb
  liftEq _  _                  _                  = False
  
instance (Ord k, Eq1 m, Monad m) => Eq1 (Open k m) where
  liftEq eq (Open ea)         (Open eb)         = liftEq eq ea eb
  liftEq eq (d1a `Update` d2a) (d1b `Update` d2b) = liftEq eq d1a d1b && liftEq eq d2a d2b
  liftEq eq (Abs ba)           (Abs bb)           = liftEq (liftEq eq) ba bb
  liftEq eq (da `Fix` x)       (db `Fix` x')      = liftEq eq da db && x == x'
  liftEq _  _                  _                  = False
    
    
instance (Ord k, Show k, Show a) => Show (Repr k a) where
  showsPrec = showsPrec1
  
instance (Ord k, Show k) => Show1 (Repr k) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Repr k a -> ShowS
  liftShowsPrec f g i e = case e of
    Var a     -> showsUnaryWith f "Var" i a
    c `At` x  -> showsBinaryWith f' showsPrec "At" i c x
    Val _ b   -> showsUnaryWith f' "val" i b
    Let en s  -> showsBinaryWith f'' f' "Let" i en s
    Prim p    -> showsUnaryWith f'' "Prim" i p
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Comps k m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Comps k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Comps e        -> showsUnaryWith f' "Closed" i e
    c1 `Concat` c2 -> showsBinaryWith f' f' "Concat" i c1 c2
    Block b        -> showsUnaryWith f'' "Block" i b
    c `Hide` x     -> showsBinaryWith f' showsPrec "Hide" i c x
    App o e c      -> showsTrinaryWith f' f' f' "App" i o e c
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
  
instance (Ord k, Show k, Show1 m, Monad m) => Show1 (Open k m) where
  liftShowsPrec
    :: forall a. (Int -> a -> ShowS)
    -> ([a] -> ShowS)
    -> Int -> Open k m a -> ShowS
  liftShowsPrec f g i e = case e of
    Open e        -> showsUnaryWith f' "Open" i e
    d1 `Update` d2 -> showsBinaryWith f' f' "Concat" i d1 d2
    Abs b          -> showsUnaryWith f'' "Abs" i b
    o `Fix` x      -> showsBinaryWith f' showsPrec "Fix" i o x
    where
      f' :: forall f. Show1 f => Int -> f a -> ShowS
      f' = liftShowsPrec f g
      
      g' :: forall f . Show1 f => [f a] -> ShowS
      g' = liftShowList f g
      
      f'' :: forall f g . (Show1 f, Show1 g) => Int -> f (g a) -> ShowS
      f'' = liftShowsPrec f' g'
      
      
instance S.Local a => S.Local (Nec a) where local_ = Req . S.local_
instance S.Self a => S.Self (Nec a) where self_ = Req . S.self_

instance S.Self a => S.Self (Repr k a) where self_ = Var . S.self_
instance S.Local a => S.Local (Repr k a) where local_ = Var . S.local_
  
instance S.Field (Repr (Tag k) a) where
  type Compound (Repr (Tag k) a) = Repr (Tag k) a
  e #. i = Comps e `At` Key i

instance Num (Repr k a) where
  fromInteger = Prim . fromInteger
  a + b = Prim (Embed a + Embed b)
  a - b = Prim (Embed a - Embed b)
  a * b = Prim (Embed a * Embed b)
  abs = Prim . abs . Embed
  signum = Prim . signum . Embed
  negate = Prim . negate . Embed
  
instance Fractional (Repr k a) where
  fromRational = Prim . fromRational
  a / b = Prim (Embed a / Embed b)
  
instance IsString (Repr k a) where
  fromString = Prim . fromString

instance S.Lit (Repr k a) where
  unop_ op = Prim . Unop op . Embed
  binop_ op a b = Prim (Binop op (Embed a) (Embed b))

    
instance Show (IOPrimTag a) where
  showsPrec i _ = errorWithoutStackTrace "show: IOPrimTag"

-- | Built-in representations for primitive types
primOpen :: Ord k => Prim (Repr (Tag k) a) -> Open (Tag k) (Repr (Tag k)) a
primOpen (Number d)  = errorWithoutStackTrace "eval: number #unimplemented"
primOpen (Text s)    = errorWithoutStackTrace "eval: text #unimplemented"
primOpen (Bool b)    = boolOpen b
primOpen (IOError e) = errorWithoutStackTrace "eval: ioerror #unimplemented"
      
-- | Bool
boolOpen :: Ord k => Bool -> Open (Tag k) (Repr (Tag k)) a
boolOpen b = (Abs . M.singleton (Key "match")
  . Scope) (Var (B Self) S.#. if b then "ifTrue" else "ifFalse")
  
