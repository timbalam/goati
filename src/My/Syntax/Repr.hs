{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( Check, runCheck, buildBlock
  , module My.Syntax.Vocabulary
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr
import qualified My.Types.Syntax.Class as S
import My.Syntax.Vocabulary
import My.Util (Collect(..), (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Trans (lift)
import Control.Monad.Free
import qualified Control.Monad.Free.Church as FC
import Data.Bifunctor
import Data.Bitraversable
import Data.Coerce (coerce)
import Data.List (elemIndex, nub)
import GHC.Exts (IsString(..))
import qualified Data.Map as M
import Bound.Scope (abstract)


-- | Applicative checking of definitions
newtype Check a = Check (Collect [DefnError] a)
  deriving (Functor, Applicative)
  
runCheck :: Check a -> Either [DefnError] a
runCheck = coerce

instance S.Self a => S.Self (Check a) where self_ i = pure (S.self_ i)
instance S.Local a => S.Local (Check a) where local_ i = pure (S.local_ i)
  
instance S.Field a => S.Field (Check a) where
  type Compound (Check a) = Check (S.Compound a)
  c #. i = c <&> (S.#. i)

instance Num a => Num (Check a) where
  fromInteger = pure . fromInteger
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum

instance Fractional a => Fractional (Check a) where
  fromRational = pure . fromRational
  (/) = liftA2 (/)

instance IsString a => IsString (Check a) where
  fromString = pure . fromString

instance S.Lit a => S.Lit (Check a) where
  unop_ op = fmap (S.unop_ op) 
  binop_ op = liftA2 (S.binop_ op)

type instance S.Member (Check (Repr (Tag k) r a)) = Check (Repr (Tag k) r a)

instance (Ord k, Show k)
  => S.Block (Check (Repr (Tag k) (P.Vis (Nec Ident) Ident) (P.Vis (Nec Ident) Ident)))  where
  type Rec (Check (Repr (Tag k) (P.Vis (Nec Ident) Ident) (P.Vis (Nec Ident) Ident))) =
    ChkRec
      ((,) [P.Vis Path Path])
      (Check (Patt (Tag k)),
       Check (Repr (Tag k) (P.Vis (Nec Ident) Ident) (P.Vis (Nec Ident) Ident)))
  block_ s = buildBlock s <&> val . fmap P.Priv
      
      
buildBlock
  :: (Ord k, Show k)
  => ChkRec
    ((,) [P.Vis Path Path])
    (Check (Patt (Tag k)),
     Check (Repr (Tag k) (P.Vis (Nec Ident) Ident) (P.Vis (Nec Ident) Ident)))
  -> Check (Open (Tag k) (P.Vis (Nec Ident) Ident) (Repr (Tag k) (P.Vis (Nec Ident) Ident)) (Nec Ident))
buildBlock s = liftA2 (buildAbs (nub ns))
  (traverse bisequenceA pas)
  (coerce (checkRec r))
  where
    (r, pas, ns) = buildRec s
      
    buildAbs
      :: (Ord k, Show k)
      => [Ident]
      -> [(Patt (Tag k), Repr (Tag k) (P.Vis (Nec Ident) Ident) (P.Vis (Nec Ident) Ident))]
      -> Rec (FC.F (M.Map Ident) Int)
      -> Open (Tag k) (P.Vis (Nec Ident) Ident) (Repr (Tag k) (P.Vis (Nec Ident) Ident)) (Nec Ident)
    buildAbs ns pas r = Abs pas' en se (Just k) where
      loc = M.mapWithKey
        (\ i f -> (Scope . buildNode (Var . B . Match <$> f) . Var . F . Var) (Opt i))
        (local r)
        
      en = map (\ i -> M.findWithDefault (atself i) i loc) ns
        
      se = (M.mapKeysMonotonic Key . M.mapWithKey
        (\ i f -> (Scope . buildNode (Var . B . Match <$> f) . Var . B . Super) (Key i)))
        (public r)
        
      pas' = map (fmap k) pas
      
      k = abstractRef ns
      
      atself :: Ident -> Scope (Ref (Tag k)) (Repr (Tag k) r) a
      atself i = Scope (B Self `atvar` i)
      
      abstractRef
        :: (Ord k, Show k)
        => [Ident]
        -> Repr (Tag k) r (P.Vis (Nec Ident) Ident)
        -> Scope (Ref (Tag k)) (Repr (Tag k) r) (Nec Ident)
      abstractRef ns o = Scope (o >>= (\ a -> case a of
        P.Priv n -> return (maybe (F (return n)) (B . Env) (elemIndex (nec id id n) ns))
        P.Pub i  -> B Self `atvar` i))
      
      
buildNode
  :: (Ord k, Show k)
  => FC.F (M.Map Ident) (Repr (Tag k) r (Var (Ref (Tag k)) a))
  -> Repr (Tag k) r (Var (Ref (Tag k)) a) -> Repr (Tag k) r (Var (Ref (Tag k)) a)
buildNode (FC.F k) = k
  (\ e _ -> e)
  (\ m e -> val (Open e `Update` Lift (Block (buildComps m) Nothing)))
  where
    buildComps = M.mapKeysMonotonic Key . M.mapWithKey 
      (\ i f -> (f . Var . B . Super) (Key i))

atvar :: a -> Ident -> Repr (Tag k) r a
atvar a k = Comps (Var a) `At` Key k
      
  
instance (Ord k, Show k, S.Local a, S.Self a) => S.Tuple (Check (Repr (Tag k) r a)) where
  type Tup (Check (Repr (Tag k) r a)) = ChkTup (Check (Repr (Tag k) r a))
  tup_ s = coerce (checkTup (coerce s :: ChkTup (Collect [DefnError] (Repr (Tag k) r a))))
    <&> (\ m -> val (Abs [] [] (buildDefns m) Nothing)) 
    where
      buildDefns = M.mapKeysMonotonic Key . M.mapWithKey
        (\ i f -> (Scope . buildNode (fmap (Var . F) f) . Var . B  . Super) (Key i))
        
  
instance (Ord k, Show k) => S.Extend (Check (Repr (Tag k) r a)) where
  type Ext (Check (Repr (Tag k) r a)) = Check (Repr (Tag k) r a)
  (#) = liftA2 update where
    update e w = val (Open e `Update` Open w)

  
letpath :: s -> ([s], Check (Patt k))
letpath s = ([s], pure Bind)

instance S.Self s => S.Self ([s], Check (Patt k)) where self_ i = letpath (S.self_ i)
instance S.Local s => S.Local ([s], Check (Patt k)) where local_ i = letpath (S.local_ i)
instance S.Field s => S.Field ([s], Check (Patt k)) where
  type Compound ([s], Check (Patt k)) = S.Compound s
  p #. i = letpath (p S.#. i)
  
type instance S.Member ([s], Check (Patt k)) = ([s], Check (Patt k))
type instance S.Member ([s], Check (Decomp k (Patt k))) = ([s], Check (Patt k))
  
instance S.VarPath s => S.Tuple ([s], Check (Decomp (Tag k) (Patt (Tag k)))) where
  type Tup ([s], Check (Decomp (Tag k) (Patt (Tag k)))) =
    ChkTup ([s], Check (Patt (Tag k)))
  tup_ t = (xs, coerce (c <&> buildDecomp)) where
    (xs, c) = checkDecomp (coerce t)
  
buildDecomp
  :: M.Map Ident (FC.F (M.Map Ident) a) -> Decomp (Tag k) a
buildDecomp m = (Decomp . M.mapKeysMonotonic Key)
  (M.map (\ (FC.F f) -> f pure (wrap . M.mapKeysMonotonic Key)) m)
  
instance S.VarPath s => S.Tuple ([s], Check (Patt (Tag k))) where
  type Tup ([s], Check (Patt (Tag k))) = ChkTup ([s], Check (Patt (Tag k)))
  tup_ d = fmap (Rest Skip) <$> S.tup_ d
  
instance S.VarPath s => S.Extend ([s], Check (Patt (Tag k))) where
  type Ext ([s], Check (Patt (Tag k))) = ([s], Check (Decomp (Tag k) (Patt (Tag k))))
  (#) = liftA2 (liftA2 Rest)


{-
instance Ord k => S.Deps (BlockDefns (Repr (Tag k) (P.Vis (Nec Ident) Ident))) where
  prelude_ (BlockB g xs) b = b' S.#: b
    where
      -- Build a pattern that introduces a local alias for each
      -- component of the imported prelude Block
      b' :: BlockDefns (Repr (Tag k) (P.Vis (Nec Ident) Ident))
      b' = S.tup_ (foldr puns S.empty_ ns) S.#= S.block_ (BlockB g xs)
      
      puns :: (S.Splus a, S.Local a) => Ident -> a -> a
      puns i a = S.local_ i S.#: a

      -- identifiers for public component names of prelude Block
      ns = nub (map (P.vis id id) (names g))
-}
