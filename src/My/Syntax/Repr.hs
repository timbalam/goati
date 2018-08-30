{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | Module with methods for desugaring and checking of syntax to the
--   core expression
module My.Syntax.Repr
  ( Check, runCheck
  , module My.Syntax.Vocabulary
  )
where

import qualified My.Types.Parser as P
import My.Types.Repr
import qualified My.Types.Syntax.Class as S
import qualified My.Syntax.Import as S (Deps(..))
import My.Syntax.Vocabulary
import My.Util (Collect(..), (<&>))
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Trans (lift)
import Control.Monad.Free.Church (MonadFree(..), F, iter)
import Data.Bifunctor
import Data.Coerce (coerce)
import Data.List (elemIndex, nub)
import GHC.Exts (IsString(..))
import qualified Data.Map as M
import Bound.Scope (abstractEither, abstract)


-- | Applicative checking of definitions
newtype Check a = Check (Collect [DefnError] a)
  deriving (Functor, Foldable, Traversable, Applicative)

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
  unop_ op = fmap (unop_ op) 
  binop_ op = liftA2 (binop_ op)

type instance S.Member (Repr (Tag k) a) = Repr (Tag k) a

instance S.Block (Check (Repr (Tag k) (P.Vis (Nec Ident) Ident)) where
  type Rec (Check (Repr (Tag k) a)) = ChkRec (Check (Patt (Tag k)), Check (Repr (Tag k) a))
  block_ s = liftA2 (buildBlock (nub ns)) (traverse bisequence pas) (checkRec (coerce r))
    <&> fmap P.Priv
    where 
      (r, pas, ns) = buildRec s
      
buildBlock
  :: [Ident]
  -> [(Patt (Tag k), Repr (Tag k) a)]
  -> Rec (F (M.Map Ident) Int)
  -> Repr (Tag k) (Nec Ident)
buildBlock ns pas r = val (Abs pas' en se) where
  loc = buildLoc (local r)
  se = M.mapKeysMonotonic Key (buildPub (public r))
  en = map (\ i -> M.lookupDefault (atself i) i loc) ns
  pas' = map (fmap (abstractRef ns)) pas
  
  atself :: Ident -> Scope Ref m a
  atself i = Scope (B Self `atvar` i)
  
  abstractRef
    :: [Ident]
    -> Repr (Tag k) (P.Vis (Nec Ident) Ident)
    -> Scope Ref (Repr (Tag k)) (Nec Ident)
  abstractRef ns o = Scope (o >>= (\ a -> case a of
    P.Priv n -> return (maybe (F (return n)) (B . Env) (lookupIndex (nec id id n) ns))
    P.Pub i  -> B Self `atvar` i))

buildLoc
  :: M.Map Ident (F (M.Map Ident) Int)
  -> M.Map Ident (Scope Ref (Repr (Tag k)) (P.Vis (Nec Ident) a))
buildLoc = M.mapWithKey
  (\ i (F f) -> Scope (f
    (\ n _ -> Var (B (Match n)))
    (\ m i -> val ((Open . Var . F . Var . P.Pub) (Opt i) `Update`
      (Abs [] [] . M.mapKeysMonotonic Key) (M.mapWithKey (\ i k -> lift (k i)) m)))
    i))
    
buildPub
  :: M.Map Ident (F (M.Map Ident) Int)
  -> M.Map Ident (Scope Ref (Repr (Tag k)) a
buildPub = M.mapWithKey
  (\ i (F f) -> Scope (f
    (\ n _ -> Var (B (Match n)))
    (\ m i -> val (Open (Var (B (Super i))) `Update`
      Abs [] [] (M.mapWithKey (\ i k -> lift (k i)) m)))
    i))

atvar :: a -> Ident -> Repr (Tag k) a
atvar a k = Comps (Var a) `At` Key k
      
  
    
instance S.Tuple (Check (Repr (Tag k) a)) where
  type Tup (Check (Repr (Tag k) a)) = ChkTup (Repr (Tag k) a)
  tup_ s = checkTup s <&> (\ m ->
      N (\ k -> k (either id (\ f -> runF f id k) <$> m)))
  
instance S.Extend (Check (Repr (Tag k) a)) where
  type Ext (Check (Repr (Tag k) a)) = Check (Repr (Tag k) a)
  (#) = liftA2 update where
    update e w = val (Open e `Update` Open w)

  
  -- | A pattern definition represents a decomposition of a value and assignment of parts.
-- Decomposed paths are checked for overlaps, and leaf 'let' patterns are returned in 
-- pattern traversal order.
newtype Patt p = Patt { runPatt :: ([P.Vis Path Path], p) }
newtype Decomp s = Decomp { runDecomp :: ([P.Vis Path Path], s) }
  

letpath :: Pun (P.Vis Path Path) p -> Patt p
letpath (Pun s p) = Patt [s] p

instance (S.Self p) => S.Self (Patt p) where self_ i = letpath (S.self_ i)
instance (S.Local p) => S.Local (Patt p) where local_ i = letpath (S.local_ i)
instance (S.Field p) => S.Field (Patt p) where
  type Compound (Patt a p) = Pun (S.Compound a) (S.Compound p)
  p #. i = letpath (p S.#. i)
  
instance S.Let s => S.Let (Decomp s) where
  type Lhs (Decomp a) = S.Lhs s
  type Rhs (Decomp a) = Patt a (S.Rhs s)
  l #= Patt p = Decomp (fmap (l #=) p)
  
instance S.Sep s => S.Sep (Decomp a s) where
  Decomp p1 #: Decomp p2 = Decomp (liftA2 (#:) p1 p2)

  
type instance Member (Patt a p)) = Patt a (S.Member p)
  
instance S.Tuple (Patt a (Check (N p))) where
  type Tup (Patt a (Check (N p))) =
    Tup (ChkStmts (Patt a (Check p)) (Decomp a (Node (Check p)))
  tup_ (Tup m) = Patt (traverse
    (\ (e :? xs) ->
      liftA2 (:?) (bitraverse runPatt runDecomp e) (traverse runPatt xs))
    m <&> (\ m ->
      M.traverseWithkey (\ i c -> checkStmts i (checkNode <$> c)) m <&> (\ m ->
      N (\ k -> k (either id (\ f -> runF f id k) <$> m)))))
          

instance S.Extend p => S.Extend (Patt a (Check (N p))) where
  type Ext (Patt (N p) a) = Patt (N p) a
  Patt (xs1, c1) # Patt (xs2, c2) = Patt (xs1 <> xs2, liftA2 ext c1 c2) where
    ext f g = N (\ k -> runN f k S.# runN g k)
    
  
{- 

--type instance S.Member (EBuilder k (P.Vis (Nec Ident) Ident)) =
--  Check (Repr (Tag k) (P.Vis (Nec Ident) Ident))

-}

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
  
  

-- | Build a set of definitions for a 'Tuple' expression
buildTup
  :: (Ord k, Show k)
  => TupDefns (Collect [DefnError] (Repr (Tag k) a))
  -> Collect [DefnError] (M.Map Ident (Scope (Ref (Tag k)) (Repr (Tag k)) a))
buildTup (TupDefns g xs) = liftA2 substexprs (lnode g) (rexprs xs)
  where
    substexprs pubn vs = pubn' where
      pubn' = M.map (f . abstractRef) pubn
      f = (>>= (vs'!!))
      vs' = map lift vs
      
      abstractRef = abstractEither (bind (Left . Super . Key) Right)
  
    -- Right-hand side values to be assigned
    rexprs xs = sequenceA xs
    
    -- Left-hand side paths determine constructed shape
    lnode
      :: (Ord k, Show k) => Defns Ident Paths
      -> Collect [DefnError] (M.Map Ident (Repr (Tag k) (Bind Ident Int)))
    lnode g = M.mapWithKey (flip getGroup) <$> group
      where
        group :: (Ord k, Show k) => Collect [DefnError] (M.Map Ident (Group k Int))
        group = (disambigpub . build g . map pure) [0..]
  
    

    
-- | Wrapper to instantiate a path extractor
newtype Extract = Extract { extract :: forall a. S.Path a => a -> a }

instance S.Self Extract where self_ i = Extract (S.#. i)

instance S.Field Extract where
  type Compound Extract = Extract
  Extract f #. i = Extract (\ e -> f e S.#. i)
  

    
