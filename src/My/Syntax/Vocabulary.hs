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
  
  
  
-- | The lhs of an assignment is a single name or a name and nested lhs.
data ChkPath p = ChkPath Ident (forall x . x -> (p -> x) -> x) -- church-encoded 'Maybe s'

newtype ChkStmts a s = ChkStmts (M.Map Ident ([a], Either a s))

instance S.Self (ChkPath p) where self_ i = ChkPath i (\ nothing _ -> nothing)
instance S.Local (ChkPath p) where local_ i = ChkPath i (\ nothing _ -> nothing)
  
instance S.RelPath p => S.Field (ChkPath p) where
  type Compound (ChkPath p) = ChkPath p
  ChkPath i maybe #. k = ChkPath i (\ _ just -> just (maybe (S.self k) (#. k)))
  
instance (S.Let s, S.Rhs s ~ a) => S.Let (ChkStmts s a) where
  type Lhs (ChkStmts s a) = ChkPath (S.Lhs s)
  type Rhs (ChkStmts s a) = a
  ChkPath i maybe #= a = (ChkStmts . M.singleton i . (,) []) (maybe (Left a) (Right . (#= a)))
  
instance S.Sep s => S.Sep (ChkStmts s a) where
  ChkStmts m1 #: ChkStmts m2 = ChkStmts (M.unionWith f m1 m2) where
    f (xs1, Left x  ) (xs2, e       ) = ([x1]++xs1++xs2, e         )
    f (xs1, e       ) (xs2, Left x  ) = (xs1++[x]++xs2 , e         )
    f (xs1, Right s1) (xs2, Right s2) = (xs1++xs2      , s1 S.#: s2)
    
instance S.Splus (ChkStmts s a) where
  S.empty_ = ChkStmts M.empty

-- | A 'Tuple' definition associates a group of paths with values.
newtype ChkTup s a = ChkTup (ChkStmts s a)

-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun a b = Pun a b

pun :: S.Let s => Pun (S.Lhs s) (S.Rhs s) -> ChkTup s (S.Rhs s)
pun (Pun p a) = ChkTup (p #= a)

instance (S.Local a, S.Self b) => S.Self (Pun a b) where self_ i = Pun (S.self_ i) (S.self_ i)
instance (S.Local a, S.Local b) => S.Local (Pun a b) where
  local_ i = Pun (S.self_ i) (S.local_ i)

instance (S.Field a, S.Field b) => S.Field (Pun a b) where
  type Compound (Pun a b) = Pun (S.Compound a) (S.Compound b)
  Pun a b #. k = Pun (a S.#. k) (b S.#. k)

instance (S.Let s, S.Rhs s ~ a) => S.Self (ChkTup s a) where self_ i = pun (S.self_ i)
instance (S.Let s, S.Rhs s ~ a) => S.Local (ChkTup s a) where local_ i = pun (S.local_ i)

instance  (S.Let s, S.Rhs s ~ a) => S.Field (ChkTup s a) where
  type Compound (ChkTup s a) = Pun (S.Compound (S.Lhs s)) (S.Compound a)
  p #. k = pun (p S.#. k)

instance S.Let s => S.Let (ChkTup s a) where
  type Lhs (ChkTup s a) = ChkPath (S.Lhs s)
  type Rhs (ChkTup s a) = a
  p #= a = ChkTup (p #= a)

instance S.Sep s => S.Sep (ChkTup s a) where
  ChkTup s1 #: ChkTup s2 = ChkTup (s1 #: s2)
  
instance S.Splus (ChkTup s a) where empty_ = ChkTup S.empty_


-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value, indicating that the path is to be 
-- checked for ambiguity but not assigned a value.
data ChkRec s a = ChkRec
  { local :: ChkStmts s (Maybe a)
  , public :: ChkStmts s (Maybe a)
  }
  
decl :: ChkPath s -> ChkRec s a
decl (ChkPath i maybe) = ChkRec
  { local = S.empty_
  , public = ChkStmts (M.singleton i ([], maybe (Left Nothing) Right))
  }
  
instance S.Self (ChkRec s a) where
  self_ i = decl (S.self_ i)
  
instance S.RelPath s => S.Field (ChkRec s a) where
  type Compound (ChkRec s a) = ChkPath s
  p #. k = decl (p S.#. k)

instance S.Let (ChkRec s a) where
  type Lhs (ChkRec s a) = ChkPatt s
  type Rhs (ChkRec s a) = a
  Patt b #= es = b { errors = errors b <> es }

instance S.Sep s => S.Sep (ChkRec s a) where
  ChkRec{local=l1,public=s1} #: ChkRec{local=l2,public=s2} =
    ChkRec { local = l1 S.#: l2, public = s1 #: s2 }

instance S.Splus (ChkRec s a) where
  empty_ = ChkRec{local=S.empty_,public=S.empty_}


-- | A pattern definition represents the simultaneous decomposing a value into distinct
-- parts and the assignment of the parts
newtype ChkDecomp s a = ChkDecomp (ChkStmts s a)

letpath :: Pun P.VarPath -> Patt
letpath p = Patt (introVis p mempty)
    
matchPun :: S.Let s => Pun (S.Lhs s) (S.Rhs s) -> ChkDecomp s (S.Rhs s)
matchPun (Pun p a) = ChkDecomp (p #= a)

checkDecomp :: DecompDefns -> Patt
checkDecomp (DecompDefns (Patt b) m) =
  Patt (b { errors = errors b <> checkMatches }) where
    checkMatches = foldMap disambig m

  
instance (S.Let s, S.Self (S.Lhs s), S.Self (S.Rhs s), S.Rhs s ~ a)
  => S.Self (ChkDecomp s a)
  where
    self_ i = matchPun (S.self_ i)
instance (S.Let s, S.Local (S.Lhs s), S.Self (S.Rhs s), S.Rhs s ~ a)
  => S.Local (ChkDecomp s a)
  where
    local_ i = matchPun (S.local_ i)

instance S.Field (ChkDecomp s a) where
  type Compound (ChkDecomp s a) = Pun (Pun P.VarPath)
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


checkBlock :: BlockDefns -> Check
checkBlock (BlockDefns{errors=e,local=l,public=s}) =
  e <> checkVis (M.intersectionWith (,) l s) <> checkLoc l <> checkPub s
  where
    -- Generate errors for any identifiers with both public and private 
    -- definitions
    checkVis = M.foldMapWithKey (const . Check . pure . OlappedVis)
    checkLoc = foldMap disambig
    checkPub = foldMap disambig
      
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

