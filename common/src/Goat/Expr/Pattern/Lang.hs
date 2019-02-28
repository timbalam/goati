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
  , Bindings(..)
  , Define(..), Redefine(..), crosswalkPatternWith
  , Pattern(..)
  , crosswalkMatches
  , C(..), runC, sendC, hoistC
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
     :: forall a . Path Label a
     -> Control Either (Path Label a)
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
     :: forall a . a
     -> C (Control These) (Path Label a)
    }

setPath :: SetChain -> SetPath
setPath (SetChain f) = SetPath (sendC . choist toThese . f . Leaf)
  where
    toThese
     :: Either (Public a) (Local a) 
     -> These (Public a) (Local a)
    toThese = either This That

instance IsString SetPath where
  fromString s = setPath (fromString s)

instance Field_ SetPath where
  type Compound SetPath = Relative SetChain
  p #. k = setPath (p #. k)

type M r f a =
  C r
    (Bindings
      (NonEmpty Int)
      f
      --(Pattern r (Redefine (NonEmpty Int) (Pattern r) f) ())
      (Pattern r (Define f) ())
      a)
      
newtype SetPattern =
  SetPattern {
    getPattern
     :: forall a . a
     -> M (Control These) (Path Label) a
    }

setPattern :: SetPath -> SetPattern
setPattern (SetPath f) = SetPattern (fmap Result . f)

instance IsString SetPattern where
  fromString s = setPattern (fromString s)
        
instance Field_ SetPattern where
  type Compound SetPattern = Relative SetChain
  p #. n = setPattern (p #. n)

instance Block_ SetPattern where
  type Stmt SetPattern = MatchPattern
  block_ ms = 
    SetPattern
      (crosswalkPatternWith
        getPattern
        (runC (getDecomp (block_ ms)) Decomp))

instance Extend_ SetPattern where
  type Ext SetPattern = SetDecomp
  p # SetDecomp m =
    SetPattern
      (crosswalkPatternWith
        getPattern 
        (runC m DecompAndBind p))

newtype SetDecomp =
  SetDecomp {
    getDecomp
     :: C (Control These)
          (Define (Path Label) SetPattern)
    }

instance Block_ SetDecomp where
  type Stmt SetDecomp = MatchPattern
  block_ [] = SetDecomp nil
  block_ (m:ms) =
    SetDecomp
      (Define <$> crosswalkMatches matchPattern (m:|ms))


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
     :: C (Control These) (Path Label SetPattern)
    }

matchPun
 :: Pun SetChain SetPattern -> MatchPattern
matchPun (Pun (SetChain f) a) =
  setPath (SetChain (choist toPub . f)) #= a
  where
    toPub
     :: Either (Public a) (Local a)
     -> Either (Public a) (Local a)
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
  SetPath f #= a = MatchPattern (f a)

matchPatternProof :: SomeMatch -> MatchPattern
matchPatternProof = run . fromMatch
