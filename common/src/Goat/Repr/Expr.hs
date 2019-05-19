{-# LANGUAGE ExistentialQuantification, FlexibleContexts, GeneralizedNewtypeDeriving, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, RankNTypes, LambdaCase #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang.Class'.
module Goat.Repr.Expr
  ( module Goat.Repr.Expr
  , Bound(..), Map(..), Text
  ) where

-- import Goat.Repr.Assoc
import Goat.Repr.Pattern
import Goat.Util (abstractEither, (<&>))
import Control.Applicative (Alternative(..), Const(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (MonadTrans(..))
import Data.Bifunctor
import Data.Functor (($>))
import Data.These (these, These(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.String (IsString(..))
import Data.Traversable (fmapDefault, foldMapDefault)
import qualified Data.Monoid as Monoid (Alt(..))
import Data.Semigroup (Option(..))
import Data.Functor.Plus (Plus(..))
import Bound (Scope(..), Var(..), Bound(..))
import Bound.Scope (hoistScope, abstract)
  

-- | Runtime value representation
data Repr f a =
    Var a 
  | Repr (Expr f (Repr f) a)
  deriving (Foldable, Traversable)

emptyRepr :: Repr f a
emptyRepr = Repr Null

instance Functor f => Functor (Repr f) where
  fmap = liftM
  
instance Functor f => Applicative (Repr f) where
  pure = Var
  (<*>) = ap

instance Functor f => Monad (Repr f) where
  return = pure
  Repr m >>= f = Repr (m >>>= f)

instance Functor f => MonadBlock (Abs f) (Repr f) where
  wrapBlock f = Repr (Block f)

-- |
data Expr f m a =
    Number Double
  | Text Text
  | Bool Bool
  | Block (Abs f m a)
  | Null
  | Sel (m a) Text
  | Add (m a) (m a)
  | Sub (m a) (m a)
  | Mul (m a) (m a)
  | Div (m a) (m a)
  | Pow (m a) (m a)
  | Eq (m a) (m a)
  | Ne (m a) (m a)
  | Lt (m a) (m a)
  | Le (m a) (m a)
  | Gt (m a) (m a)
  | Ge (m a) (m a)
  | Or (m a) (m a)
  | And (m a) (m a)
  | Not (m a)
  | Neg (m a)

hoistExpr
 :: (Functor r, Functor m)
 => (forall x . m x -> n x) -> Expr r m a -> Expr r n a
hoistExpr f = \case
  Number d -> Number d
  Text t   -> Text t
  Bool b   -> Bool b
  Block r  -> Block (hoistAbs f r)
  Null     -> Null
  Sel a k  -> Sel (f a) k
  Add a b  -> Add (f a) (f b)
  Sub a b  -> Sub (f a) (f b)
  Mul a b  -> Mul (f a) (f b)
  Div a b  -> Div (f a) (f b)
  Pow a b  -> Pow (f a) (f b)
  Eq  a b  -> Eq  (f a) (f b)
  Ne  a b  -> Ne  (f a) (f b)
  Lt  a b  -> Lt  (f a) (f b)
  Le  a b  -> Le  (f a) (f b)
  Gt  a b  -> Gt  (f a) (f b)
  Ge  a b  -> Ge  (f a) (f b)
  Or  a b  -> Or  (f a) (f b)
  And a b  -> And (f a) (f b)
  Not a    -> Not (f a)
  Neg a    -> Neg (f a)

instance (Traversable m, Traversable r) => Functor (Expr r m)
  where 
    fmap = fmapDefault
  
instance (Traversable m, Traversable r) => Foldable (Expr r m) 
  where
    foldMap = foldMapDefault

instance
  (Traversable m, Traversable r) => Traversable (Expr r m)
  where
    traverse f = \case
      Number d -> pure (Number d)
      Text t   -> pure (Text t)
      Bool b   -> pure (Bool b)
      Block r  -> Block <$> traverse f r
      Null     -> pure Null
      Sel a k  -> traverse f a <&> (`Sel` k)
      Add a b  -> op Add a b
      Sub a b  -> op Sub a b
      Mul a b  -> op Mul a b
      Div a b  -> op Div a b
      Pow a b  -> op Pow a b
      Eq  a b  -> op Eq  a b
      Ne  a b  -> op Ne  a b
      Gt  a b  -> op Gt  a b
      Ge  a b  -> op Ge  a b
      Lt  a b  -> op Lt  a b
      Le  a b  -> op Le  a b
      Or  a b  -> op Or  a b
      And a b  -> op And a b
      Not a    -> Not <$> traverse f a
      Neg a    -> Neg <$> traverse f a
      where
        op g a b = g <$> traverse f a <*> traverse f b

instance Functor r => Bound (Expr r) where
  Number d >>>= _ = Number d
  Text t   >>>= _ = Text t
  Bool b   >>>= _ = Bool b
  Block r  >>>= f = Block (r >>>= f)
  Null     >>>= _ = Null
  Sel a k  >>>= f = Sel (a >>= f) k
  Add a b  >>>= f = Add (a >>= f) (b >>= f)
  Sub a b  >>>= f = Sub (a >>= f) (b >>= f)
  Mul a b  >>>= f = Mul (a >>= f) (b >>= f)
  Div a b  >>>= f = Div (a >>= f) (b >>= f)
  Pow a b  >>>= f = Pow (a >>= f) (b >>= f)
  Eq  a b  >>>= f = Eq  (a >>= f) (b >>= f)
  Ne  a b  >>>= f = Ne  (a >>= f) (b >>= f)
  Gt  a b  >>>= f = Gt  (a >>= f) (b >>= f)
  Ge  a b  >>>= f = Ge  (a >>= f) (b >>= f)
  Lt  a b  >>>= f = Lt  (a >>= f) (b >>= f)
  Le  a b  >>>= f = Le  (a >>= f) (b >>= f)
  Or  a b  >>>= f = Or  (a >>= f) (b >>= f)
  And a b  >>>= f = And (a >>= f) (b >>= f)
  Not a    >>>= f = Not (a >>= f)
  Neg a    >>>= f = Neg (a >>= f)
--

-- type Ident = Text
type VarName a b c = 
  Either (Public a) (Either (Local b) c)

absFromBindings
 :: MonadBlock (Abs Components) m
 => Bindings Declares Decompose m (VarName Ident Ident a)
 -> m (VarName b Ident a)
 -> Abs Components m (VarName b Ident a)
absFromBindings bs m = abs
  where
    -- bs scopes outer to inner: super, env
    ((Local lp, Public pp), bs') =
      squashBindings <$>
        transverseBindings
          componentsBlockFromDeclares
          (hoistBindings (lift . lift) bs)
    
    (ns, penv) = captureComponents lp
    
     -- abstract local and public variables before binding outer scoped values
    bsAbs = abstractVarName ns . return <$> bs'
    bsSuper = letBind (Match pp (lift (lift m))) bsAbs
    bsEnv = letBind (Match lp (lift (lift penv))) bsSuper
    
     -- bind abstracted local variables to pattern returned by 
     -- 'componentsBlockFromDeclares'
    abs = Abs (Let (hoistBindings (lift . lift) bsEnv >>>= id))
    
    captureComponents
     :: MonadBlock (Abs Components) m
     => Components a -> ([Maybe Ident], m (VarName b Ident c))
    captureComponents (Inside (Extend r _)) =
      wrapBlock . Abs . Define . Inside <$>
        sequenceA
          (Extend
            (Map.mapWithKey
              (\ n _ ->
                ( [Just n]
                , [return (Right (Left (Local n)))]
                ))
              r)
            ([Nothing], []))
      


componentsBlockFromDeclares
 :: MonadBlock (Abs Components) m
 => Declares a
 -> ( (Local (Components ()), Public (Components ()))
    , Bindings
       (Parts Decompose Components)
       Decompose
       (Scope (Local Int) (Scope (Local Int) m))
       a
    )
componentsBlockFromDeclares (Declares (Local lr) (Public pr) k) =
  ( (Local lp, Public pp)
  , liftBindings2 Parts 
      (embedBindings
        (Define . 
          Match lp . 
          lift . lift .
          wrapComponents)
        (hoistBindings lift lbs))
      (hoistBindings (hoistScope lift) pbs)
  )
  where
    (pp, pbs) =
      componentsBlockFromNode (reprFromAssigns . k <$> pr)
    (lp, lbs) =
      componentsBlockFromNode (reprFromAssigns . k <$> lr)
      
    wrapComponents
     :: MonadBlock (Abs Components) m
     => Components a -> m a
    wrapComponents p =
      wrapBlock (Abs (Define (return <$> p)))
    
    reprFromAssigns
     :: MonadBlock (Abs Components) m
     => Assigns (Map Text) (NonEmpty a)
     -> Int -> [Scope (Local Int) m a]
    reprFromAssigns m =
      reprFromAssignsWith
        reprFromNode
        (reprFromLeaf <$> m)


reprFromLeaf
 :: (Foldable t, Monad m) => t a -> b -> [m a]
reprFromLeaf t _ = Monoid.getAlt (foldMap (pure . return) t)

reprFromNode
 :: MonadBlock (Abs Components) m
 => Components ()
 -> Block Components (Scope (Local Int) m) a
 -> Int -> [Scope (Local Int) m a]
reprFromNode p bs i = [Scope (wrapBlock abs)] where
  abs =
    Abs
      (hoistBindings lift
        (letBind (Match p (B (Local i))) (F . return <$> bs)))

-- | 'reprFromAssignsWith kp asgs i' generates a value from set of assigns 'asgs'.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
reprFromAssignsWith
 :: Monad m
 => (Components () ->
      Block Components (Scope (Local Int) m) a ->
      Int ->
      [Scope (Local Int) m a])
 -> Assigns (Map Text) (Int -> [Scope (Local Int) m a])
 -> Int -> [Scope (Local Int) m a]
reprFromAssignsWith kp =
  merge .
    iterAssigns
      (\ r ->
        case componentsBlockFromNode (merge <$> r) of
          (p, m) -> kp p m)
  where
    merge = these id id mappend

-- | 'componentsBlockFromNode r' generates a pattern matching the fields of
-- 'r' and a corresponding binding value with identical fields with values generated by the fields of 'r'.
componentsBlockFromNode
 :: Monad m
 => Map Text (Int -> [Scope (Local Int) m a])
 -> ( Components ()
    , Bindings Components p (Scope (Local Int) m) a
    )
componentsBlockFromNode r = (p, bs)
  where
    x = Extend r (pure . Scope . return . B . Local)
    p = Inside (x $> pure ())
    xm = mapWithIndex (\ i f -> f i) x
    bs = Define (Inside xm)

{-
fieldsReprsFromNode
 :: Monad m
 => Map Text (Int -> [Scope (Local Int) m a])
 -> ([Text], [[Scope (Local Int) m a]])
fieldsReprsFromNode r = 
  Map.foldMapWithKey
    (\ n m -> ([n], [m]))
    (mapWithIndex (\ i f -> f i) r)
-}    

    

-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVarName
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) (Scope (Public p) m) (VarName q a b)
abstractVarName ns m =
  Right <$> abstractLocal ns (abstractPublic m)
  where
    abstractPublic = abstractEither id
    
abstractLocal
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (Either (Local a) b)
 -> Scope (Local Int) m (Either (Local a) b)
abstractLocal ns =
  abstract (\case
    Left (Local n) -> Local <$> elemIndex (Just n) ns
    Right _ -> Nothing)


-- | Marker type for source-external references
newtype Import a = Import { getImport :: a }
