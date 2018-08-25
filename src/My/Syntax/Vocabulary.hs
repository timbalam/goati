{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, StandaloneDeriving, ScopedTypeVariables, TupleSections #-}

-- | The '[DefnError]' type implements an abstract interpretation for validating sets of 
-- definitions made using the syntax classes for duplicated names, overlapping definitions, 
-- etc. 
module My.Syntax.Vocabulary
  ( DefnError(..) )
  where

import qualified My.Types.Parser as P
import My.Types.Repr (Ident)
import My.Types.Classes (MyError(..))
import qualified My.Types.Syntax.Class as S
import Control.Applicative (liftA2)
import Control.Monad (ap)
import Control.Monad.Free.Church (MonadFree(..), F)
import Data.Semigroup
import Data.String (IsString(..))
import Data.Functor.Plus (Plus(..), Alt(..))
import Data.Typeable
import qualified Data.Map as M
--import qualified Data.Set as S


-- | Errors from binding definitions
data DefnError =
    OlappedMatch (P.Path P.Key)
  -- ^ Error if a pattern specifies matches to non-disjoint parts of a value
  | OlappedSet P.VarPath
  -- ^ Error if a group assigns to non-disjoint paths
  | OlappedVis Ident
  -- ^ Error if a name is assigned both publicly and privately in a group
  deriving (Eq, Show, Typeable)
  
instance MyError DefnError where
  displayError (OlappedMatch p) = "Ambiguous destructuring of path " ++ show p
  displayError (OlappedSet p) = "Ambiguous assignment to path " ++ show p
  displayError (OlappedVis i) = "Variable assigned with multiple visibilities " ++ show i
  
  
-- | Applicative checking of definitions
newtype Check = Check [DefnError]
  deriving (Semigroup, Monoid)

instance S.Self Check where self_ _ = mempty
instance S.Local Check where local_ _ = mempty
  
instance S.Field Check where
  type Compound Check = Check
  es #. _ = es

instance Num Check where
  fromInteger = mempty
  (+) = (<>)
  (-) = (<>)
  (*) = (<>)
  negate = id
  abs = id
  signum = id

instance Fractional Check where
  fromRational = mempty
  (/) = (<>)

instance IsString Check where
  fromString = mempty

instance S.Lit Check where
  unop_ _ = id
  binop_ _ = (<>)

type instance S.Member Check = Check

instance S.Tuple Check where
  type Tup Check = TupDefns
  tup_ = checkTup 

instance S.Block Check where
  type Rec Check = BlockDefns
  block_ = checkBlock
  
  
  
-- | A 'Path' is a sequence of nested names. We represent as an insert function for
-- nested paths.
data Path = Path (forall a. Amb a -> M.Map Ident (Amb a))

instance S.Self Path where self_ i = Path (M.singleton i)
instance S.Local Path where local_ i = Path (M.singleton i)
  
instance S.Field Path where
  type Compound Path = Path
  Path f #. i = Path (f . wrap . M.singleton i)


-- | A 'Tuple' definition associates a group of paths with values.
data TupDefns = TupDefns Check (M.Map Ident (Amb DefnError))

checkTup :: TupDefns -> Check
checkTup (TupDefns es m) = foldMap disambig m <> es

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun a = Pun (forall x. S.RelPath x => x) a

pun :: Pun P.VarPath -> TupDefns
pun (Pun (Path intro) p) = TupDefns mempty (intro (pure (OlappedSet p)))

instance S.Self a => S.Self (Pun a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance S.Local a => S.Local (Pun a) where local_ i = Pun (S.self_ i) (S.local_ i)

instance S.Field a => S.Field (Pun a) where
  type Compound (Pun a) = Pun (S.Compound a)
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)

instance S.Self TupDefns where self_ i = pun (S.self_ i)
instance S.Local TupDefns where local_ i = pun (S.local_ i)

instance S.Field TupDefns where
  type Compound TupDefns = Pun P.VarPath
  pb #. k = pun (pb S.#. k)

instance S.Let TupDefns where
  type Lhs TupDefns = Pun P.VarPath
  type Rhs TupDefns = Check
  Pun (Path intro) p #= es = TupDefns es (intro (pure (OlappedSet p)))

instance S.Sep TupDefns where
  TupDefns e1 g1 #: TupDefns e2 g2 = TupDefns (e1 <> e2) (M.unionWith (<!>) g1 g2)
  
instance S.Splus TupDefns where empty_ = TupDefns mempty M.empty


-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value, indicating that the path is to be 
-- checked for ambiguity but not assigned a value.
data BlockDefns = BlockDefns
  { errors :: Check
  , local :: M.Map Ident (Amb DefnError)
  , public :: M.Map Ident (Amb DefnError)
  }

introVis :: Pun P.VarPath -> Check -> BlockDefns
introVis (Pun (Path intro) p@(P.Priv _)) e =
  BlockDefns { errors = e, local = intro (pure (OlappedSet p)), public = M.empty }
introVis (Pun (Path intro) p@(P.Pub _)) e =
  BlockDefns { errors = e, local = M.empty, public = intro (pure (OlappedSet p)) }

decl :: Pun (P.Path P.Key) -> BlockDefns
decl (Pun p r) = introVis (Pun p (P.Pub r)) mempty

checkBlock :: BlockDefns -> Check
checkBlock (BlockDefns{errors=e,local=l,public=s}) =
  e <> checkVis (M.intersectionWith (,) l s) <> checkLoc l <> checkPub s
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.foldMapWithKey (const . Check . pure . OlappedVis)
    checkLoc = foldMap disambig
    checkPub = foldMap disambig
  
instance S.Self BlockDefns where self_ k = decl (S.self_ k)
  
instance S.Field BlockDefns where
  type Compound BlockDefns = Pun (P.Path P.Key)
  b #. k = decl (b S.#. k)

instance S.Let BlockDefns where
  type Lhs BlockDefns = Patt
  type Rhs BlockDefns = Check
  Patt b #= es = b { errors = errors b <> es }

instance S.Sep BlockDefns where
  BlockDefns{errors=e1,local=l1,public=s1} #: BlockDefns{errors=e2,local=l2,public=s2} =
    BlockDefns
      { errors = e1 <> e2
      , local = M.unionWith (<!>) l1 l2
      , public = M.unionWith (<!>) s1 s2
      }

instance S.Splus BlockDefns where
  empty_ = BlockDefns{errors=mempty,local=M.empty,public=M.empty}


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
newtype Patt = Patt BlockDefns
data DecompDefns = DecompDefns Patt (M.Map Ident (Amb DefnError))

letpath :: Pun P.VarPath -> Patt
letpath p = Patt (introVis p mempty)
    
matchPun :: Pun Patt -> DecompDefns
matchPun (Pun (Pun (Path intro) r) p) =
  DecompDefns p (intro (pure (OlappedMatch r)))

checkDecomp :: DecompDefns -> Patt
checkDecomp (DecompDefns (Patt b) m) =
  Patt (b { errors = errors b <> checkMatches }) where
    checkMatches = foldMap disambig m

  
instance S.Self DecompDefns where self_ i = matchPun (S.self_ i)
instance S.Local DecompDefns where local_ i = matchPun (S.local_ i)

instance S.Field DecompDefns where
  type Compound DecompDefns = Pun (Pun P.VarPath)
  p #. k = matchPun (p S.#. k)

instance S.Let DecompDefns where
  type Lhs DecompDefns = Pun (P.Path P.Key)
  type Rhs DecompDefns = Patt
  Pun (Path intro) r #= p = DecompDefns p (intro (pure (OlappedMatch r)))

instance S.Sep DecompDefns where
  DecompDefns (Patt b1) g1 #: DecompDefns (Patt b2) g2 =
    DecompDefns (Patt (b1 S.#: b2)) (M.unionWith (<!>) g1 g2)

instance S.Splus DecompDefns where empty_ = DecompDefns (Patt S.empty_) M.empty
 
 
instance S.Self Patt where self_ i = letpath (S.self_ i)
instance S.Local Patt where local_ i = letpath (S.local_ i)
  
instance S.Field Patt where
  type Compound Patt = Pun P.VarPath
  v #. k = letpath (v S.#. k)

type instance S.Member Patt = Patt

instance S.Tuple Patt where
  type Tup Patt = DecompDefns
  tup_ d = checkDecomp d
  
instance S.Extend Patt where
  type Ext Patt = Patt
  Patt b1 # Patt b2 = Patt (b1 S.#: b2)
  

-- | Validate that a finished tree has unambiguous paths and construct 
-- an expression that reflects the tree of assigned values.
--
-- If there are any ambiguous paths, returns them as list of 'OlappedSet'
-- errors.
--
-- Paths with missing 'Nothing' values represent paths that are validated but
-- not assigned, and unassigned trees of paths are not included in output.
disambig
  :: Amb DefnError -> Check
disambig (Overlap _ Nothing)  = mempty
disambig (Overlap e (Just b)) = Check (pure e) <> disambig b
disambig (Disjoint m)         = foldMap disambig m
      
-- | Tree of paths with one or values contained in leaves and zero or more
-- in internal nodes
--
-- Semigroup and monoid instances defined will union subtrees recursively
-- and accumulate values.
data Amb a = a `Overlap` Maybe (Amb a) | Disjoint (M.Map Ident (Amb a))
  deriving (Functor, Foldable, Traversable)
  
instance Applicative Amb where
  pure a = a `Overlap` Nothing
  (<*>) = ap
  
instance Monad Amb where
  return = pure
  
  a `Overlap` Nothing >>= k = k a
  a `Overlap` Just as >>= k = k a <!> (as >>= k)
  Disjoint fa >>= k = Disjoint (M.map (>>= k) fa)
  
instance MonadFree (M.Map Ident) Amb where
  wrap = Disjoint
  
instance Alt Amb where
  x `Overlap` Just a <!> b = (Overlap x . Just) (a <!> b)
  x `Overlap` Nothing <!> b = x `Overlap` Just b
  a <!> x `Overlap` Nothing = x `Overlap` Just a
  a <!> x `Overlap` Just b = (Overlap x . Just) (a <!> b)
  Disjoint fa <!> Disjoint fb = Disjoint (M.unionWith (<!>) fa fb)

