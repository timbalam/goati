{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( Check, runCheck, buildBlock, Name, buildBrowse
  , module My.Syntax.Vocabulary
  )
where

import qualified My.Types.Syntax as P
import My.Types.Repr
import My.Types.Error (DefnError)
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


type Name = P.Vis (Nec Ident) Ident

-- | Applicative checking of definitions
newtype Check a = Check (Collect [DefnError Ident] a)
  deriving (Functor, Applicative)
  
runCheck :: Check a -> Either [DefnError Ident] a
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
  

type instance S.Member (Check (Repr s (Tag k) a)) = Check (Repr s (Tag k) a)

instance (Ord k, Show k) => S.Block (Check (Repr (Browse Name) (Tag k) Name)) where
  type Rec (Check (Repr (Browse Name) (Tag k) Name)) =
    ChkRec ((,) [P.Vis Path Path])
      (Check (Patt (Tag k)), Check (Repr (Browse Name) (Tag k) Name))
      
  block_ s = buildAbsParts s <&> (\ (pas, en, se, k) ->
    P.Priv <$> val (Abs pas en (Browse (Just k) se)))
  
buildBrowse
  :: (Ord k, Show k)
  => [ChkRec
    ((,) [P.Vis Path Path])
    (Check (Patt (Tag k)), Check (Repr (Browse Name) (Tag k) Name))]
  -> Check (Browse Name (Tag k) (Repr (Browse Name) (Tag k) (Nec Ident)))
buildBrowse s = buildAbsParts s <&> appAbsParts where
      appAbsParts (pas, en, se, k) = b where
        b = appAbs emptyBlock e pas en o
        o = Browse (Just k) se
        e = Val (Block b) (Abs pas en o)
        emptyBlock = Block (fromMap M.empty)
    
instance (Ord k, Show k) => S.Block (Check (Repr Assoc (Tag k) Name)) where
  type Rec (Check (Repr Assoc (Tag k) Name)) =
    ChkRec ((,) [P.Vis Path Path])
      (Check (Patt (Tag k)), Check (Repr Assoc (Tag k) Name))
  
  block_ s = buildBlock s <&> fmap P.Priv
    
    
buildBlock 
  :: (Ord k, Show k)
  => [ChkRec
    ((,) [P.Vis Path Path])
    (Check (Patt (Tag k)), Check (Repr Assoc (Tag k) Name))]
  -> Check (Repr Assoc (Tag k) (Nec Ident))
buildBlock s = buildAbsParts s <&> (\ ( pas, en, se, _) -> val (Abs pas en (Assoc se)))
      
      
buildAbsParts
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => [ChkRec
    ((,) [P.Vis Path Path])
    (Check (Patt (Tag k)), Check (Repr s (Tag k) Name))]
  -> Check
    ([(Patt (Tag k), Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident))],
     [Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident)],
     M.Map (Tag k) (Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident)),
     Repr s (Tag k) Name -> Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident))
buildAbsParts s = liftA2 (buildAbsParts' (nub ns))
  (traverse bisequenceA pas)
  (coerce (checkRec r))
  where
    (r, pas, ns) = buildRec s
      
    buildAbsParts'
      :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
      => [Ident]
      -> [(Patt (Tag k), Repr s (Tag k) Name)]
      -> VisMap (FC.F (M.Map Ident) Int)
      -> ([(Patt (Tag k), Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident))],
          [Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident)],
          M.Map (Tag k) (Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident)),
          Repr s (Tag k) Name -> Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident))
    buildAbsParts' ns pas vm = (pas', en, se, k) where
      loc = M.mapWithKey
        (\ i f -> (Scope . buildNode (Var . B . Match <$> f) . Var . F . Var) (Opt i))
        (local vm)
        
      en = map (\ i -> M.findWithDefault (atself i) i loc) ns
        
      se = (M.mapKeysMonotonic Key . M.mapWithKey
        (\ i f -> (Scope . buildNode (Var . B . Match <$> f) . Var . B . Super) (Key i)))
        (public vm)
        
      pas' = map (fmap k) pas
      
      k = abstractRef ns
      
      atself :: Ident -> Scope (Ref (Tag k)) (Repr s (Tag k)) a
      atself i = Scope (B Self `atvar` i)
      
      abstractRef
        :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
        => [Ident]
        -> Repr s (Tag k) Name
        -> Scope (Ref (Tag k)) (Repr s (Tag k)) (Nec Ident)
      abstractRef ns o = Scope (o >>= (\ a -> case a of
        P.Priv n -> return (maybe (F (return n)) (B . Env) (elemIndex (nec id id n) ns))
        P.Pub i  -> B Self `atvar` i))
      
      
buildNode
  :: (Ord k, Show k, Functor (s (Tag k)), IsAssoc s)
  => FC.F (M.Map Ident) (Repr s (Tag k) (Var (Ref (Tag k)) a))
  -> Repr s (Tag k) (Var (Ref (Tag k)) a) -> Repr s (Tag k) (Var (Ref (Tag k)) a)
buildNode (FC.F k) = k
  (\ e _ -> e)
  (\ m e -> val (Open e `Update` Lift (Block (buildComps m))))
  where
    buildComps = fromMap . M.mapKeysMonotonic Key . M.mapWithKey 
      (\ i f -> (f . Var . B . Super) (Key i))

atvar :: a -> Ident -> Repr s (Tag k) a
atvar a k = Comps (Var a) `At` Key k

      
  
instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s, S.Local a, S.Self a) => S.Tuple (Check (Repr s (Tag k) a)) where
  type Tup (Check (Repr s (Tag k) a)) =
    ChkTup (Check (Repr s (Tag k) a))
    
  tup_ s = coerce (checkTup s')
    <&> (\ m -> val (Abs [] [] (buildDefns m))) where
    s' = coerce s
      :: [ChkTup (Collect [DefnError Ident] (Repr s (Tag k) a))]

    buildDefns =
      fromMap . M.mapKeysMonotonic Key . M.mapWithKey
        (\ i f ->
          (Scope . buildNode (fmap (Var . F) f) . Var . B
            . Super) (Key i))
        
  
instance (Ord k, Show k, Functor (s (Tag k)), IsAssoc s) => S.Extend (Check (Repr s (Tag k) a)) where
  type Ext (Check (Repr s (Tag k) a)) = Check (Repr s (Tag k) a)
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
  tup_ cs = (xs, coerce (m <&> buildDecomp)) where
    (xs, m) = checkDecomp (coerce cs)
  
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
