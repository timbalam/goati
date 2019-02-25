{-# LANGUAGE TypeFamilies, RankNTypes #-}
module Goat.Expr.Pattern.Lang
  where

import Goat.Comp (run)
import Goat.Lang.Field
  ( Field_(..)
  , SomeVarChain, fromVarChain, SomePath, fromPath
  )
import Goat.Lang.Let
  ( Let_(..)
  , SomeMatch, fromMatch 
  )
import Goat.Lang.Ident (IsString(..))
import Goat.Lang.Block (Block_(..))
import Goat.Lang.Extend (Extend_(..))
import Goat.Expr.Pattern
  ( Path(..), wrapPath
  , Label, lsingleton
  , Control, csingleton, choist
  , Local(..), Public(..)
  , Define, definePattern
  , Pattern(..)
  , crosswalkNonEmpty
  )
import Data.Align (Align(..))
import Data.List.NonEmpty (NonEmpty(..))
import Data.These (These(..), these, mergeTheseWith)
import Data.Semigroup ((<>))
import Data.Void (absurd)


-- | Binding 
data Relative a = Self | Parent a

instance IsString a => IsString (Relative a) where
  fromString "" = Self
  fromString s = Parent (fromString s)

instance Field_ a => Field_ (Relative a) where
    type Compound (Relative a) = Compound a
    m #. k = Parent (m #. k)
    
newtype SetChain =
  SetChain {
    getChain
      :: forall a .
          Path Label a -> Control Either (Path Label a)
    }

instance IsString SetChain where
  fromString s =
    SetChain
      (csingleton (fromString s) . Right . Local)

instance Field_ SetChain where
  type
    Compound SetChain = Relative SetChain
  
  Self #. n =
    SetChain (csingleton n . Left . Public)
  Parent (SetChain f) #. n =
    SetChain (f . wrapPath . lsingleton n)

setChainProof :: SomeVarChain -> Relative SetChain
setChainProof = run . fromVarChain
      
newtype SetPath =
  SetPath {
    getPath
     :: forall a .
          a -> Control Either (Path Label a)
    }

setPath :: SetChain -> SetPath
setPath (SetChain f) = SetPath (f . Leaf)

instance IsString SetPath where
  fromString s = setPath (fromString s)
        
instance Field_ SetPath where
  type Compound SetPath = Relative SetChain
  p #. n = setPath (p #. n)

setPathProof :: SomePath -> SetPath
setPathProof = run . fromPath


newtype SetPattern =
  SetPattern {
    getPattern ::
      Pattern (Define (Control These) (Path Label)) SetPath
    }

instance IsString SetPattern where
  fromString s = SetPattern (Bind (fromString s))

instance Field_ SetPattern where
  type Compound SetPattern = Relative SetChain
  p #. k = SetPattern (Bind (p #. k))

instance Block_ SetPattern where
  type Stmt SetPattern = MatchPattern
  block_ [] = SetPattern (Decomp nil absurd)
  block_ (m:ms) =
    SetPattern
      (Decomp
        (crosswalkNonEmpty matchPattern (m:|ms))
        (pure . getPattern))

instance Extend_ SetPattern where
  type Ext SetPattern = SetDecomp
  SetPattern p # SetDecomp r = SetPattern (extend' p r) where
    alignPatterns
     :: Align r
     => r (NonEmpty x) -> (x -> NonEmpty a)
     -> r (NonEmpty y) -> (y -> NonEmpty a)
     -> (forall xx . r (NonEmpty xx) -> (xx -> NonEmpty a) -> p)
     -> p
    alignPatterns ra ka rb kb f =
      f (alignWith
          (mergeTheseWith (fmap This) (fmap That) (<>))
          ra
          rb)
        (mergeTheseWith ka kb (<>))
  
    extend' (Decomp r k) r' =
      alignPatterns r k r' (pure . getPattern) Decomp
    extend' (Bind a) r' =
      DecompAndBind r' (pure . getPattern) a
    extend' (DecompAndBind r k a) r' =
      alignPatterns r k r' (pure . getPattern) DecompAndBind a

newtype SetDecomp =
  SetDecomp {
    getDecomp
     :: Define (Control These) (Path Label) (NonEmpty SetPattern)
    }

instance Block_ SetDecomp where
  type Stmt SetDecomp = MatchPattern
  block_ [] = SetDecomp nil
  block_ (m:ms) =
    SetDecomp (crosswalkNonEmpty matchPattern (m:|ms))


-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun
  :: Let_ s => Pun (Lhs s) (Rhs s) -> s
pun (Pun p a) = p #= a

instance (IsString p, IsString a) => IsString (Pun p a) where
  fromString n = Pun (fromString n) (fromString n)

instance (Field_ p, Field_ a) => Field_ (Pun p a) where
  type Compound (Pun p a) = Pun (Compound p) (Compound a)
  Pun p a #. n = Pun (p #. n) (a #. n)


newtype MatchPattern =
  MatchPattern {
    matchPattern
      :: Define (Control These) (Path Label) SetPattern
    }

matchPun
 :: Pun SetPath SetPattern -> MatchPattern
matchPun (Pun (SetPath f) a) = SetPath (choist toPub . f) #= a
  where
    toPub
     :: Either (Public a) (Local a) -> Either (Public a) (Local a)
    toPub = Left . Public . either getPublic getLocal
      
instance IsString MatchPattern where
  fromString s = matchPun (fromString s)

instance Field_ MatchPattern where
  type Compound MatchPattern =
    Pun (Relative SetChain) (Relative SetChain)
  p #. k = matchPun (p #. k)

instance Let_ MatchPattern where
  type Lhs MatchPattern = SetPath
  type Rhs MatchPattern = SetPattern
  SetPath p #= a =
    MatchPattern (definePattern (Bind (choist toThese . p)) a)
    where
      toThese
       :: Either (Public a) (Local a) 
       -> These (Public a) (Local a)
      toThese = either This That

matchPatternProof :: SomeMatch -> MatchPattern
matchPatternProof = run . fromMatch
