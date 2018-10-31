{-# LANGUAGE FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable, GeneralizedNewtypeDeriving, RankNTypes, ScopedTypeVariables, InstanceSigs, TypeFamilies, PolyKinds, StandaloneDeriving, FlexibleContexts, TypeOperators, MultiParamTypeClasses, FunctionalDependencies, OverloadedStrings #-}

-- | This module along with Goat.Types.Eval contain the core data type representations.
-- This is a pure data representation suitable for optimisation,
-- before conversion to the data type from Goat.Types.Eval for evaluation.
-- The core data type implements the typeclass encoding of the Goat syntax.
module Goat.Expr
  ( Repr(..), Expr(..), Value(..)
  , toEval
  , Ref(..), ref
  , Nec(..), nec, Name
  , S.Ident, S.Unop(..), S.Binop(..)
  , Var(..), Bound(..), Scope(..)
  , module Goat.Types.DynMap
  )
  where
  

import qualified Goat.Syntax.Class as S
import qualified Goat.Eval as Eval (Repr(..))
import Goat.Eval hiding (Repr)
import Goat.Error
import Goat.Types.Paths.Patt ()
import Goat.Types.Paths.Rec ()
import Goat.Types.DynMap
import qualified Goat.Syntax.Syntax as P
import Goat.Util (showsUnaryWith, showsBinaryWith, 
  showsTrinaryWith, (<&>), traverseMaybeWithKey, Compose(..))
import Control.Applicative (liftA2, (<|>))
import Control.Monad (ap, (>=>))
import Control.Monad.Reader
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Free
import Control.Monad.Writer
import Data.Bitraversable
import Data.List (elemIndex)
import qualified Data.Map as M
import Data.String (IsString(..))
import qualified Data.Text as T
import Bound
import Prelude.Extras
  

-- | Runtime value representation
data Repr k f a =
    Var a
  | Repr (Value (Expr k f (Repr k f) a))
  deriving (Functor, Foldable, Traversable)
  
data Expr k f m a =
    m a `At` k 
    -- ^ Field access
  | m a `Update` m a
    -- ^ Chain definitions
  | Abs
      [(Patt f Bind, Scope Ref m a)]
      [Scope Ref m a]
      (f (Scope Ref m a))
  | Lift (f (m a))
  | Unop S.Unop (m a)
  | Binop S.Binop (m a) (m a)
  deriving (Functor, Foldable, Traversable)
  
instance (Ord k, Functor f) => Bound (Expr k f) where
  m `At` k       >>>= f = (m >>= f) `At` k
  m1 `Update` m2 >>>= f = (m1 >>= f) `Update` (m2 >>= f)
  Abs pas en kv  >>>= f = Abs
    (fmap (fmap (>>>= f)) pas)
    (fmap (>>>= f) en)
    (fmap (>>>= f) kv)
  Lift kv        >>>= f = Lift (fmap (>>= f) kv)
  Unop op m      >>>= f = Unop op (m >>= f)
  Binop op m1 m2 >>>= f = Binop op (m1 >>= f) (m2 >>= f)
  
  
-- | Marker type for self- and env- references
data Ref = Match Int | Env Int | Self deriving (Eq, Show)

ref :: (Int -> a) -> (Int -> a) -> a -> Ref -> a
ref f _ _ (Match i) = f i 
ref _ g _ (Env i)   = g i
ref _ _ a Self      = a


-- | Permit bindings with a default value 
data Nec a = Req a | Opt a
  deriving (Eq, Show)

nec :: (a -> b) -> (a -> b) -> Nec a -> b
nec f _ (Req a) = f a
nec _ g (Opt a) = g a

type Name = P.Vis (Nec Ident) Ident

toEval
  :: (S.Self k, Ord k, Foldable f, Applicative f)
  => Repr k (Dyn' k) Name
  -> Res k (Eval (Dyn k f))
toEval r = evals <$> traverse resolveVars r where
  resolveVars (P.Pub n) = S.self_ n
  resolveVars (P.Priv n) = nec S.local_ (ReaderT . opt) n where
    opt n ns = pure (maybe
      (\ _ _ -> (Eval.Repr
        . Block
        . const
        . dyn)
          (DynMap Nothing M.empty)) 
      (\ i en _ -> en !! i)
      (elemIndex n ns))
    
evals
  :: (S.Self k, Ord k, Foldable f, Applicative f)
  => Repr k (Dyn' k) (Eval (Dyn k f)) -> Eval (Dyn k f)
evals (Var ev) en se = ev en se
evals (Repr v) en se = case v of 
  Block e  -> evals' e en se
  Number d -> Eval.Repr (Number d)
  Text t   -> Eval.Repr (Text t)
  Bool b   -> Eval.Repr (Bool b)
  where
  evals' (m `At` k) en se =
    self (evals m en se) `dynLookup` k
  evals' (m1 `Update` m2) en se =
    evals m1 en se `dynConcat` evals m2  en se
  evals' (Unop op m) en se = fromSelf
    (S.unop_ op (self (evals m en se)))
  evals' (Binop op m1 m2) en se = fromSelf (S.binop_
    op
    (self (evals m1 en se))
    (self (evals m2 en se)))
  evals' (Lift dkv) en se = (Eval.Repr
    . Block
    . const
    . dyn
    . runDyn')
      (fmap (\ m -> evals m en se) dkv)
  evals' (Abs pas en' dkv) en _ = Eval.Repr (Block k)
    where
      k se = (dyn . runDyn')
        (fmap (\ m -> instantiate' m en se) dkv) where
        instantiate' = 
          evals . instantiate (ref (rvs'!!) (ren'!!) rse)
        
        rse = return (\ _ _ -> se)
        rvs' = foldMap
          (\ (p, a) -> let r = instantiate' a en se in
            match p r <&> (\ r' -> return (\ _ _ -> r')))
          pas
        ren' = map (return . instantiate') en'
        

  
instance (Ord k, Functor f)
  => Applicative (Repr k f) where
  pure = Var
  (<*>) = ap
  
instance (Ord k, Functor f) => Monad (Repr k f) where
  return = pure
  Var a  >>= f = f a
  Repr v >>= f = Repr (fmap (>>>= f) v)

instance (Ord k, Functor f, Eq1 f, Eq a)
  => Eq (Repr k f a) where
  Var a == Var a' = a == a'
  Repr v == Repr v' = v == v'
  
instance (Ord k, Functor f, Eq1 f) => Eq1 (Repr k f) where
  (==#) = (==)

instance (Ord k, Functor f, Eq1 f, Monad m, Eq1 m, Eq a)
  => Eq (Expr k f m a) where
  m `At` k           == m' `At` k'       =
    m ==# m' && k == k'
  Lift kv            == Lift kv'         =
    fmap Lift1 kv ==# fmap Lift1 kv'
  (m1 `Update` m2) == (m1' `Update` m2') =
    m1 ==# m1' && m2 ==# m2'
  Abs ps en kv     == Abs ps' en' kv'    =
    ps ==# ps' && en ==# en' && kv ==# kv'
  Unop op m        == Unop op' m'        = op == op' && m ==# m'
  Binop op m1 m2   == Binop op' m1' m2'  = op == op' &&
    m1 ==# m2 && m1' ==# m2'
  _                == _                  = False
  
instance (Ord k, Functor f, Eq1 f, Monad m, Eq1 m) 
  => Eq1 (Expr k f m) where
  (==#) = (==)
    
    
instance (Ord k, Show k, Functor f, Show1 f, Show a)
  => Show (Repr k f a) where
  showsPrec d (Var a) = showsUnaryWith showsPrec "Var" d a
  showsPrec d (Repr v) = showsUnaryWith showsPrec "Repr" d v
  
instance (Ord k, Show k, Functor f, Show1 f)
  => Show1 (Repr k f) where
  showsPrec1 = showsPrec
 
instance (Ord k, Show k, Functor f, Show1 f, Monad m, Show1 m, Show a)
  => Show (Expr k f m a) where
  showsPrec d e = case e of
    m `At` x       ->
      showsBinaryWith showsPrec1 showsPrec "At" d m x
    m1 `Update` m2 ->
      showsBinaryWith showsPrec1 showsPrec1 "Concat" d m1 m2
    Abs pas en kv  ->
      showsTrinaryWith showsPrec1 showsPrec
        showsPrec1 "Abs" d pas en kv
    Lift kv        ->
      showsUnaryWith showsPrec1 "Lift" d (fmap Lift1 kv)
    Unop op m      ->
      showsBinaryWith showsPrec showsPrec1 "Unop" d op m
    Binop op m1 m2 ->
      showsTrinaryWith showsPrec showsPrec1
        showsPrec1 "Binop" d op m1 m2
    
instance (Ord k, Show k, Functor f, Show1 f, Monad m, Show1 m)
  => Show1 (Expr k f m) where
  showsPrec1 = showsPrec
 
 
instance S.Local a => S.Local (Nec a) where
  local_ i = Req (S.local_ i)
  
nume = error "Num (Repr k f a)"

instance Num (Writer [e] (Repr k f a)) where
  fromInteger = pure . Repr . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Frac (Repr k f a)"
  
instance Fractional (Writer [e] (Repr k f a)) where
  fromRational = pure . Repr . fromRational
  (/) = frace
  
instance IsString (Writer [e] (Repr k f a)) where
  fromString = pure . Repr . fromString

instance S.Lit (Writer [e] (Repr k f a)) where
  unop_ op = fmap (Repr . Block . Unop op)
  binop_ op = liftA2 (binop' op) where
    binop' op x y = Repr (Block (Binop op x y))

instance S.Self a => S.Self (Writer [e] (Repr k f a)) where
  self_ n = (pure . Var) (S.self_ n)
instance S.Local a => S.Local (Writer [e] (Repr k f a)) where
  local_ n = (pure . Var) (S.local_ n)
  
instance S.Self k => S.Field (Writer [e] (Repr k f a)) where
  type Compound (Writer [e] (Repr k f a)) =
    Writer [e] (Repr k f a)
  m #. n = m <&> (\ r -> (Repr . Block) (r `At` S.self_ n))


instance (S.Self k, Ord k, S.Self a, S.Local a)
  => S.Tuple (Writer
    [StaticError k]
    (Repr k (Dyn' k) a)) where
  type Tup (Writer [StaticError k] (Repr k (Dyn' k) a)) =
    Tup k (Writer [StaticError k] (Repr k (Dyn' k) a))
      
  tup_ ts = dynCheckTup (foldMap (Comps . getTup) ts) <&>
    (Repr . Block
      . Lift
      . dyn
      . DynMap Nothing)
  
instance (S.Self k, Ord k)
  => S.Block (Writer
    [StaticError k]
    (Repr k (Dyn' k) (P.Vis (Nec S.Ident) a))) where
  type Rec (Writer
    [StaticError k]
    (Repr k (Dyn' k) (P.Vis (Nec S.Ident) a))) =
      Rec [P.Vis (Path k) (Path k)]
        (Patt (Decomps k) Bind, Writer [StaticError k]
          (Repr k (Dyn' k) (P.Vis (Nec S.Ident) k)))
      
  block_ rs = liftA2 evalBlock
    (dynCheckVis v)
    (traverse
      (bitraverse dynCheckPatt id)
      pas) <&> fmap P.Priv
    where
      (v, pas, ns') = buildVis rs
      
      evalBlock (Vis{private=l,public=s}) pas = Repr (Block e)
        where
          e :: Expr k (Dyn' k) (Repr k (Dyn' k)) (Nec S.Ident)
          e = Abs pas' localenv (dyn kv) where
            kv = DynMap Nothing (M.map
              (fmap (Scope . return . B . Match))
              s)
              
            pas' = map (fmap abstract') pas
            
          abstract'
            :: Repr k (Dyn' k) (P.Vis (Nec S.Ident) k)
            -> Scope Ref (Repr k (Dyn' k)) (Nec S.Ident)
          abstract' m = Scope (m >>= \ a -> case a of
            P.Pub k -> (Repr . Block) (return (B Self) `At` k)
            P.Priv n -> maybe
              (return (F (return n)))
              (return . B . Env)
              (elemIndex (nec id id n) ns'))
            
          localenv
            :: S.Self k
            => [Scope Ref (Repr k (Dyn' k)) (Nec Ident)]
          localenv = en' where
            en' = map
              (\ n -> M.findWithDefault
                ((Scope . Repr . Block)
                  (return (B Self) `At` S.self_ n))
                n
                lext)
              ns'
              
            -- extend inherited local bindings
            lext = M.mapWithKey
              (\ n m -> case runFree
                (fmap (return . B . Match) m) of
                Pure r -> Scope r
                Free dkv -> 
                  (Scope . Repr . Block) 
                    ((return . F . return) (S.local_ n)
                    `Update`
                    (Repr . Block . Lift) (dyn dkv)))
              l
      
instance Ord k
  => S.Extend (Writer [e] (Repr k f a)) where
  type Ext (Writer [e] (Repr k f a)) =
    Writer [e] (Repr k f a)
   
  (#) = liftA2 ext' where
    ext' m m' = Repr (Block (m `Update` m'))
