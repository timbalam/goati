{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, TypeFamilies, RankNTypes, LambdaCase, FlexibleInstances #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang.Class'.
module Goat.Repr.Expr
  ( module Goat.Repr.Expr
  , Map, Text, Scope(..), Var(..), Identity(..)
  , Multi, Ident, Abs(..), Block
  ) where

import Goat.Repr.Pattern
import Goat.Util (abstractEither, (<&>))
-- import Control.Applicative (Alternative(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bisequenceA, bitraverse)
import Data.Functor (($>))
import Data.These (these, These(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Semigroup ((<>))
import Data.Void (Void)
import Bound (Scope(..), Var(..), Bound(..))
import Bound.Scope (hoistScope, bitransverseScope, abstract)


-- | Runtime value representation
class Measure f b where measure :: f a -> b

class MeasureExpr f b where
  measureExpr :: Expr f (Repr b f) a -> b
instance MeasureExpr f () where measureExpr _ = ()
instance MeasureExpr f b => Measure (Expr f (Repr b f)) b where
  measure = measureExpr

data Repr b f a =
    Var a
  | Repr b (Expr f (Repr b f) a)
  deriving (Foldable, Traversable)

repr
 :: Measure (Expr f (Repr b f)) b
 => Expr f (Repr b f) a -> Repr b f a
repr f = Repr (measure f) f

emptyRepr
 :: Measure (Expr f (Repr b f)) b => Repr b f a
emptyRepr = repr (Value Null)

transRepr
 :: (Functor f, MeasureExpr f r, MeasureExpr g s)
 => (forall x. f x -> g x)
 -> Repr r f a -> Repr s g a
transRepr _f (Var a) = Var a
transRepr f (Repr _ e) = repr
  (transExpr f (hoistExpr (transRepr f) e))

bitransverseRepr
 :: (Applicative h, MeasureExpr g s)
 => (forall x x'. (x -> h x') -> f x -> h (g x'))
 -> (a -> h b)
 -> Repr r f a -> h (Repr s g b)
bitransverseRepr f g (Var a) = Var <$> g a
bitransverseRepr f g (Repr _ e) =
  repr <$> bitransverseExpr f (bitransverseRepr f) g e

instance
  (Functor f, MeasureExpr f b) => Functor (Repr b f)
  where fmap = liftM
  
instance
  (Functor f, MeasureExpr f b) => Applicative (Repr b f)
  where
    pure = Var
    (<*>) = ap

instance
  (Functor f, MeasureExpr f b) => Monad (Repr b f)
  where
    return = pure
    Var a    >>= f = f a
    Repr _ m >>= f = repr (m >>>= f)

instance
  MeasureExpr (Multi Identity) b
   => MonadBlock (Block Maybe Identity) (Repr b (Multi Identity))
  where
    wrapBlock (Abs bs) = repr (Value (Block (Abs bs'))) where
      bs' = embedBindings injectEmpty bs

      injectEmpty
       :: MeasureExpr (Multi Identity) b
       => Multi Maybe a
       -> Bindings
            (Multi Identity)
            p
            (Scope (Public Ident) (Repr b (Multi Identity)))
            a
      injectEmpty (Components x) =
        Define
          (Components
            (bimap
              (fmap return)
              (pure . maybe (lift emptyRepr) return)
              x))

-- |
data Expr f m a =
    Value (Value (Abs f (Match (f ())) m a))
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
  Value v -> Value (hoistAbs f <$> v)
  Sel a k -> Sel (f a) k
  Add a b -> Add (f a) (f b)
  Sub a b -> Sub (f a) (f b)
  Mul a b -> Mul (f a) (f b)
  Div a b -> Div (f a) (f b)
  Pow a b -> Pow (f a) (f b)
  Eq  a b -> Eq  (f a) (f b)
  Ne  a b -> Ne  (f a) (f b)
  Lt  a b -> Lt  (f a) (f b)
  Le  a b -> Le  (f a) (f b)
  Gt  a b -> Gt  (f a) (f b)
  Ge  a b -> Ge  (f a) (f b)
  Or  a b -> Or  (f a) (f b)
  And a b -> And (f a) (f b)
  Not a   -> Not (f a)
  Neg a   -> Neg (f a)

transExpr
 :: (forall x. f x -> g x)
 -> Expr f m a -> Expr g m a
transExpr f = \case
  Value v -> Value (transAbs f <$> v)
  Sel a k -> Sel a k
  Add a b -> Add a b
  Sub a b -> Sub a b
  Mul a b -> Mul a b
  Div a b -> Div a b
  Pow a b -> Pow a b
  Eq  a b -> Eq  a b
  Ne  a b -> Ne  a b
  Lt  a b -> Lt  a b
  Le  a b -> Le  a b
  Gt  a b -> Gt  a b
  Ge  a b -> Ge  a b
  Or  a b -> Or  a b
  And a b -> And a b
  Not a   -> Not a
  Neg a   -> Neg a
  where
    transAbs
     :: (forall x . f x -> g x)
     -> Abs f (Match (f ())) m a -> Abs g (Match (g ())) m a
    transAbs f (Abs bs) =
      Abs (transBindings f (transPattern (first f) bs))

bitransverseExpr
 :: Applicative h 
 => (forall x x' . (x -> h x') -> f x -> h (g x'))
 -> (forall x x' . (x -> h x') -> m x -> h (n x'))
 -> (a -> h b)
 -> Expr f m a -> h (Expr g n b)
bitransverseExpr f g h = \case
  Value v -> Value <$> traverse (bitransverseBlock f g h) v
  Sel a k -> g h a <&> (`Sel` k)
  Add a b -> op Add a b
  Sub a b -> op Sub a b
  Mul a b -> op Mul a b
  Div a b -> op Div a b
  Pow a b -> op Pow a b
  Eq  a b -> op Eq  a b
  Ne  a b -> op Ne  a b
  Lt  a b -> op Lt  a b
  Le  a b -> op Le  a b
  Gt  a b -> op Gt  a b
  Ge  a b -> op Ge  a b
  Or  a b -> op Or  a b
  And a b -> op And a b
  Not a   -> Not <$> g h a
  Neg a   -> Neg <$> g h a
  where
    op f a b = f <$> g h a <*> g h b
  
    bitransverseBlock
     :: Applicative h
     => (forall x x' . (x -> h x') -> f x -> h (g x'))
     -> (forall x x' . (x -> h x') -> m x -> h (n x'))
     -> (a -> h b)
     -> Abs f (Match (f ())) m a
     -> h (Abs g (Match (g ())) n b)
    bitransverseBlock f g h (Abs bs) =
      Abs <$>
        bitransverseBindings
          f
          (bitraverse (f pure))
          (bitransverseScope g)
          h
          bs

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
      Value v -> Value <$> traverse (traverse f) v
      Sel a k -> traverse f a <&> (`Sel` k)
      Add a b -> op Add a b
      Sub a b -> op Sub a b
      Mul a b -> op Mul a b
      Div a b -> op Div a b
      Pow a b -> op Pow a b
      Eq  a b -> op Eq  a b
      Ne  a b -> op Ne  a b
      Gt  a b -> op Gt  a b
      Ge  a b -> op Ge  a b
      Lt  a b -> op Lt  a b
      Le  a b -> op Le  a b
      Or  a b -> op Or  a b
      And a b -> op And a b
      Not a   -> Not <$> traverse f a
      Neg a   -> Neg <$> traverse f a
      where
        op g a b = g <$> traverse f a <*> traverse f b

instance Functor r => Bound (Expr r) where
  Value v >>>= f = Value ((>>>= f) <$> v)
  Sel a k >>>= f = Sel (a >>= f) k
  Add a b >>>= f = Add (a >>= f) (b >>= f)
  Sub a b >>>= f = Sub (a >>= f) (b >>= f)
  Mul a b >>>= f = Mul (a >>= f) (b >>= f)
  Div a b >>>= f = Div (a >>= f) (b >>= f)
  Pow a b >>>= f = Pow (a >>= f) (b >>= f)
  Eq  a b >>>= f = Eq  (a >>= f) (b >>= f)
  Ne  a b >>>= f = Ne  (a >>= f) (b >>= f)
  Gt  a b >>>= f = Gt  (a >>= f) (b >>= f)
  Ge  a b >>>= f = Ge  (a >>= f) (b >>= f)
  Lt  a b >>>= f = Lt  (a >>= f) (b >>= f)
  Le  a b >>>= f = Le  (a >>= f) (b >>= f)
  Or  a b >>>= f = Or  (a >>= f) (b >>= f)
  And a b >>>= f = And (a >>= f) (b >>= f)
  Not a   >>>= f = Not (a >>= f)
  Neg a   >>>= f = Neg (a >>= f)

data Value a =
    Number Double
  | Text Text
  | Bool Bool
  | Null
  | Block a
  deriving (Functor, Foldable, Traversable, Eq, Show)

instance Applicative Value where
  pure = Block
  (<*>) = ap

instance Monad Value where
  return = pure
  Number d >>= _ = Number d
  Text t   >>= _ = Text t
  Bool b   >>= _ = Bool b
  Null     >>= _ = Null
  Block a  >>= f = f a

displayValue :: (a -> String) -> Value a -> String
displayValue showa = \case
  Number d -> show d
  Text t   -> Text.unpack t
  Bool b   ->
    "<bool: " ++ if b then "true" else "false" ++ ">"
  Null     -> "{}"
  Block a  -> "{" ++ showa a ++ "}"
--


type VarName a b c = 
  Either (Public a) (Either (Local b) c)

absFromBindings
 :: MonadBlock (Block Maybe Identity) m
 => Bind Declares (Multi Identity ()) m (VarName Ident Ident a)
 -> m (VarName b Ident a)
 -> Block Maybe Identity m (VarName b Ident a)
absFromBindings bs m = abs
  where
    -- bs scopes outer to inner: super, env
    ((Local lp, Public pp), bs') =
      squashBindings <$>
        transverseBindings
          componentsBlockFromDeclares
          (hoistBindings (lift . lift) bs)
    
    (ns, env) = captureComponents lp
    
     -- abstract local and public variables before binding outer scoped values
    bsAbs = abstractVars ns . return <$> bs'
    bsSuper = letBind (Match pp (lift (lift m))) bsAbs
    bsEnv = letBind (Match lp (lift (lift env))) bsSuper
    
     -- bind abstracted local variables to pattern returned by 
     -- 'componentsBlockFromDeclares'
    abs = Abs (Let (hoistBindings (lift . lift) bsEnv >>>= id))
    
    captureComponents
     :: MonadBlock (Abs (Multi Maybe) p) m
     => Multi g a
     -> ([Maybe Ident], m (VarName b Ident c))
    captureComponents (Components (Extend r _)) =
      wrapBlock . Abs . Define . Components <$>
        bisequenceA
          (Extend
            (Map.mapWithKey
              (\ n _ ->
                ( [Just n]
                , pure (return (Right (Left (Local n))))
                ))
              r)
            ([Nothing], Nothing))
      


componentsBlockFromDeclares
 :: MonadBlock (Block Maybe Identity) m
 => Declares a
 -> ( (Local (Multi Identity ()), Public (Multi Identity ()))
    , Bindings
       (Parts (Match (Multi Identity ())) (Multi Maybe))
       p
       (Scope (Local Int) (Scope (Local Int) m))
       a
    )
componentsBlockFromDeclares (Declares (Local lr) (Public pr) k) =
  ( (Local lp, Public pp)
  , Define (Parts (Match lp lm) pc)
  )
  where
    -- public outer scope
    pc =
      hoistScope lift <$> 
        componentsFromNode (reprFromAssigns . k <$> pr)
    pp = patternFromComponents pc
    -- local inner scope
    lc =
      lift <$> componentsFromNode (reprFromAssigns . k <$> lr)
    lp = patternFromComponents lc
    
    lm =
      join
        (lift (lift (wrapBlock (Abs (Define (return <$> lc))))))
    
    reprFromAssigns
     :: MonadBlock (Block Maybe Identity) m
     => Assigns (Map Text) (NonEmpty a)
     -> Int -> NonEmpty (Scope (Local Int) m a)
    reprFromAssigns m =
      reprFromAssignsWith reprFromNode (reprFromLeaf <$> m)


reprFromLeaf :: Monad m => NonEmpty a -> b -> NonEmpty (m a)
reprFromLeaf t _ = return <$> t

reprFromNode
 :: MonadBlock (Block Maybe Identity) m
 => Multi Maybe (Scope (Local Int) m a)
 -> Int -> NonEmpty (Scope (Local Int) m a)
reprFromNode c i = pure (Scope (wrapBlock abs)) where
  p = Match (patternFromComponents c) (B (Local i))
  bs = F . return <$> Define c
  abs = Abs (hoistBindings lift (letBind p bs))

patternFromComponents
 :: (Applicative f', Applicative g')
 => Components f g a -> Components f' g' ()
patternFromComponents (Components x) =
  Components (bimap (\_ -> pure ()) (\_ -> pure ()) x)

-- | 'reprFromAssignsWith kp asgs i' generates a value from set of assigns 'asgs'.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
reprFromAssignsWith
 :: (Monad m, Applicative g)
 => (Multi g (Scope (Local Int) m a) ->
      Int ->  NonEmpty (Scope (Local Int) m a))
 -> Assigns (Map Text) (Int -> NonEmpty (Scope (Local Int) m a))
 -> Int -> NonEmpty (Scope (Local Int) m a)
reprFromAssignsWith kp =
  merge .
    iterAssigns
      (\ r -> kp (componentsFromNode (merge <$> r)))
  where
    merge = these id id (<>)

-- | 'componentsBlockFromNode r' generates a pattern matching the fields of
-- 'r' and a corresponding binding value with identical fields with values generated by the fields of 'r'.
componentsFromNode
 :: (Monad m, Applicative g)
 => Map Text (Int -> NonEmpty (Scope (Local Int) m a))
 -> Multi g (Scope (Local Int) m a)
componentsFromNode r =
  Components
    (bimapWithIndex
      (\ i f -> f i)
      (\ i _ -> pure (Scope (return (B (Local i)))))
      (Extend r ()))


-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVars
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) (Scope (Public p) m) (VarName q a b)
abstractVars ns m =
  abstractLocal ns (abstractPublic m)
  where
    abstractPublic = abstractEither (fmap Right)
    
abstractLocal
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) m (VarName p a b)
abstractLocal ns =
  abstract (\case
    Right (Left (Local n)) -> Local <$> elemIndex (Just n) ns
    _ -> Nothing)


-- | Marker type for source-external references
newtype Import a = Import { getImport :: a }
