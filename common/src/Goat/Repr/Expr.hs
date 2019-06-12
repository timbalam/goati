{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, TypeFamilies, RankNTypes, LambdaCase, FlexibleInstances, ScopedTypeVariables #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang.Class'.
module Goat.Repr.Expr
  ( module Goat.Repr.Expr
  , Scope(..), Var(..), Ident
  , Map, Text, BlockCpts, Cpts
  ) where

import Goat.Repr.Pattern
import Goat.Util (abstractEither, (<&>), (...))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.Bifunctor (bimap, first)
import Data.Bitraversable (bisequenceA, bitraverse)
import Data.Functor (($>))
import Data.These (mergeTheseWith, these, These(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Semigroup (Semigroup(..))
import Data.Void (Void)
import Bound (Scope(..), Var(..), Bound(..))
import Bound.Scope
  (hoistScope, bitransverseScope, abstract)


-- | Runtime value representation
class Measure f v where measure :: f a -> v

class MeasureExpr f v where
  measureExpr :: Expr f (Repr f v) a -> v

instance MeasureExpr f () where measureExpr _ = ()
instance
  MeasureExpr f v => Measure (Expr f (Repr f v)) v
  where
  measure = measureExpr

data Repr f v a
  = Var a
  | Repr (Value (Memo (Expr f (Repr f v)) v a))
  deriving (Foldable, Traversable)

measureRepr
 :: Measure
      (Memo (Expr f (Repr f v)) v)
      (Value b)
 => Repr f v Void -> Value b
measureRepr (Repr v) = v >>= measure

emptyRepr
 :: Repr f v a
emptyRepr = Repr Null

transRepr
 :: forall f g v w a
  . (Functor f, MeasureExpr f v, MeasureExpr g w)
 => (forall x. f x -> g x)
 -> Repr f v a -> Repr g w a
transRepr f
  = go
  where
  go :: forall a . Repr f v a -> Repr g w a
  go (Var a)
    = Var a
  
  go (Repr v)
    = Repr
        (mapMemo (transExpr f . hoistExpr go)
         <$> v)

bitransverseRepr
 :: (Applicative h, MeasureExpr g w)
 => (forall x x'. (x -> h x') -> f x -> h (g x'))
 -> (a -> h b)
 -> Repr f v a -> h (Repr g w b)
bitransverseRepr f g (Var a)
  = Var <$> g a
bitransverseRepr f g (Repr v)
  = Repr
 <$> traverse
      (traverseMemo
        (bitransverseExpr f (bitransverseRepr f) g))
      v

instance
  (Functor f, MeasureExpr f v) => Functor (Repr f v)
  where
  fmap = liftM
  
instance
  (Functor f, MeasureExpr f v)
   => Applicative (Repr f v)
  where
  pure = Var
  (<*>) = ap

instance
  (Functor f, MeasureExpr f v) => Monad (Repr f v)
  where
  return = pure
  Var a  >>= f = f a
  Repr v >>= f
    = Repr ((`memoBind` f) <$> v)
    where
    memoBind
     :: (Bound t, Monad m, Measure (t m) v)
     => Memo (t m) v a
     -> (a -> m b)
     -> Memo (t m) v b
    memoBind (Memo _ e) f = memo (e >>>= f) 
  

instance
  ( Functor f, Functor g, Functor h
  , MeasureExpr (TagCpts f g h) v
  )
   => MonadBlock
        (BlockCpts f) (Repr (TagCpts f g h) v)
  where
  wrapBlock (Block (Extend c m))
    = Repr
        (Comp
          (memo
            (Ext
              (Define (DeclareCpts c))
              (fromMaybe emptyRepr m))))

-- |
data Expr f m a
  = Ext
      (Bindings f f
        (Scope (Super Ident)
          (Scope (Public Ident) m))
        a)
      (m a)
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
  deriving (Eq, Show)

hoistExpr
 :: (Functor r, Functor m)
 => (forall x . m x -> n x)
 -> Expr r m a -> Expr r n a
hoistExpr f
  = \case
    Ext bs a
     -> Ext
          (hoistBindings
            (hoistScope (hoistScope f)) bs)
          (f a)
    
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
transExpr f
  = \case
    Ext bs a ->
      Ext (transBindings f (transPattern f bs)) a
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

bitransverseExpr
 :: Applicative h 
 => (forall x x' . (x -> h x') -> f x -> h (g x'))
 -> (forall x x' . (x -> h x') -> m x -> h (n x'))
 -> (a -> h b)
 -> Expr f m a -> h (Expr g n b)
bitransverseExpr f g h
  = \case
    Ext bs a
     -> Ext
     <$> bitransverseBindings
          f
          f
          (bitransverseScope
                (bitransverseScope g))
          h
          bs
     <*> g h a
    
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

instance
  (Traversable m, Traversable r)
   => Functor (Expr r m)
  where 
  fmap = fmapDefault
  
instance
  (Traversable m, Traversable r)
   => Foldable (Expr r m) 
  where
  foldMap = foldMapDefault

instance
  (Traversable m, Traversable r)
   => Traversable (Expr r m)
  where
  traverse f
    = \case
      Ext bs a
       -> Ext <$> traverse f bs <*> traverse f a
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
  Ext bs a >>>= f
    = Ext (bs >>>= lift . lift . f) (a >>= f)
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

data Value a
  = Number Double
  | Text Text
  | Bool Bool
  | Null
  | Comp a
  deriving (Eq, Show, Functor, Foldable, Traversable)

displayValue
 :: (a -> String) -> Value a -> String
displayValue showa
  = \case
    Number d
     -> show d
    
    Text t
     -> Text.unpack t
    
    Bool b
     -> "<bool: "
     ++ if b then "true" else "false"
     ++ ">"
    
    Null
     -> "{}"
    
    Comp a
     -> showa a

instance Applicative Value where
  pure = Comp
  (<*>) = ap

instance Monad Value where
  return = pure
  Number d >>= _ = Number d
  Text t   >>= _ = Text t
  Bool b   >>= _ = Bool b
  Null     >>= _ = Null
  Comp a   >>= f = f a

-- |
data Memo f v a = Memo v (f a)
  deriving (Functor, Foldable, Traversable)

memo :: Measure f v => f a -> Memo f v a
memo f = Memo (measure f) f

unmemo :: Memo f v a -> f a
unmemo (Memo _ fa) = fa

mapMemo
 :: Measure g w
 => (f a -> g b) -> Memo f v a -> Memo g w b
mapMemo f (Memo _ fa) = memo (f fa)

traverseMemo
 :: (Functor h, Measure g w)
 => (f a -> h (g b))
 -> Memo f v a
 -> h (Memo g w b)
traverseMemo f (Memo _ fa) = memo <$> f fa
--

data TagCpts f g h a
  = DeclareCpts (Cpts f a)
  | MatchCpts (Cpts g a)
  | Other (h a)
  deriving (Functor, Foldable, Traversable)


type VarName a b c
  = Either (Public a) (Either (Local b) c)

abstractBindings
 :: (Applicative f, Functor g, Functor h
    , MonadBlock (BlockCpts f) m
    )
 => Bindings (Inside (Ambig f) Declares) (Cpts g)
      m
      (VarName Ident Ident a)
 -> Bindings (TagCpts f g h) (TagCpts f g h)
      (Scope (Super Ident)
        (Scope (Public Ident) m))
        (VarName b Ident a)
abstractBindings bs = toAbs bsEnv
  where
  -- bs scopes outer to inner: env, super
  (lp, bs')
    = squashBindings <$>
        transverseBindings
          (fmap (transBindings declareComponents)
            . componentsBlockFromDeclares)
          (hoistBindings (lift . lift)
            (transPattern MatchCpts bs))
  
  declareComponents (Parts a b)
    = Parts (DeclareCpts a) (DeclareCpts b)
  (ns, env) = captureComponents lp
  
   -- abstract local and public variables before binding outer scoped values
  bsAbs
    = abstractVars ns . return <$> bs'
  bsEnv
    = Match (DeclareCpts lp)
        (return (lift (lift env)))
        bsAbs
  
   -- bind abstracted local variables to pattern returned by 
   -- 'componentsBlockFromDeclares'
  toAbs
   :: (Functor p, Functor f, Monad m)
   => Bindings (Parts p f) p
        (Scope (Super Ident) m)
        (Scope (Local Int)
          (Scope (Public Ident) m)
          a)
   -> Bindings f p
        (Scope (Super Ident)
          (Scope (Public Ident) m))
        a
  toAbs bs
    = Index
        (hoistBindings
          (lift . hoistScope lift) bs
         >>>= hoistScope lift)
    
  captureComponents
   :: (Applicative f, MonadBlock (BlockCpts f) m)
   => Cpts f a
   -> ([Maybe Ident], m (VarName b Ident c))
  captureComponents (Inside kv)
    = bitraverse
        (\ n
         -> ( [Just n]
            , pure (return (Right (Left (Local n))))
            ))
        (\ ()
         -> ([Nothing], ()))
        (Extend
          (Map.mapWithKey const kv) ())
   <&> \ (Extend kv mb)
        -> wrapBlock 
            (Block (Extend (Inside kv) Nothing))
      

componentsBlockFromDeclares
 :: (Applicative g, MonadBlock (BlockCpts g) m)
 => Inside (Ambig g) Declares a
 -> ( Cpts g ()
    , Bindings 
        (Parts (Cpts g) (Cpts g))
        p
        (Scope (Local Int) (Scope (Super Ident) m))
        a
    )
componentsBlockFromDeclares
  (Inside (Declares (Local lr) (Public pr) k))
  = (lp, Define (Parts lc pc))
  where
  -- public inner scope
  pc
    = lift
   <$> reprFromNode
        (iterAssigns reprFromNode . k <$> pr)
  
  -- local outer scope
  lc
    = localReprFromNode
        lr
        (iterAssigns reprFromNode . k)
  lp = patternFromComponents lc
  
  localReprFromNode
   :: (Applicative g, MonadBlock (BlockCpts g) m)
   => Map Text x
   -> (x
       -> These
            (Ambig g a)
            (Cpts g (Scope (Super Ident) m a)))
   -> Cpts g (Scope (Local Int) (Scope b m) a)
  localReprFromNode r k
    = Inside
        (mapWithIndex
          (\ i a -> merge i (k a))
          r)
    where
    merge i
      = mergeTheseWith
          (fmap return)
          (fmap (hoistScope lift)
            . (`superWrapComponents` Local i))
          (<>)

reprFromNode
 :: (Applicative h, MonadBlock (BlockCpts h) m)
 => Map Text
      (These 
        (Ambig h a)
        (Cpts h (Scope (Super Ident) m a)))
 -> Cpts h (Scope (Super Ident) m a)
reprFromNode kv
  = Inside (Map.mapWithKey merge kv)
  where
    merge n
      = mergeTheseWith
          (fmap return)
          (`superWrapComponents` Super n)
          (<>)

superWrapComponents
 :: ( Functor f, Applicative h
    , MonadBlock (Block f) m
    )
 => f (Scope (Super Ident) m a)
 -> b
 -> h (Scope b m a)
superWrapComponents c b
  = pure
      (Scope
        (wrapBlock
          (Block (Extend c' m))))
  where
  m = pure (return (B b))
  c' = liftCpt <$> c
  
  liftCpt
   :: Monad m
   => Scope (Super Ident) m a
   -> Scope (Super Ident) (Scope (Public Ident) m)
        (Var b (m a))
  liftCpt 
    = hoistScope lift . fmap (F . return)

patternFromComponents
 :: Applicative f => Cpts f a -> Cpts f ()
patternFromComponents (Inside kv)
  = Inside (kv $> pure ())

-- | 'reprFromAssignsWith kp asgs i' generates a value from set of assigns 'asgs'.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
reprFromAssignsWith
 :: Semigroup m
 => (Map Text m -> Ident -> m)
 -> Assigns (Map Text) (Ident -> m)
 -> Ident -> m
reprFromAssignsWith kp asgs n
  = merge n
      (iterAssigns
        (\ r
         -> kp (Map.mapWithKey merge r))
        asgs)
  where
  merge n th = these id id (<>) th n

-- | 'localComponentsFromNode r' generates a pattern matching the fields of
-- 'r' and a corresponding binding value with identical fields with values generated by the fields of 'r'.
localComponentsFromNode
 :: Monad m
 => Map Text
      (Int -> Ambig f (Scope (Local Int) m a))
 -> Cpts f (Scope (Local Int) m a)
localComponentsFromNode r
  = Inside r'
  where
  Extend r' _
    = bimapWithIndex
        (\ i f -> f i)
        (\ _ () -> ())
        (Extend r ())


-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVars
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int)
      (Scope (Public p) m) (VarName q a b)
abstractVars ns m
  = abstractLocal ns (abstractPublic m)
  where
  abstractPublic = abstractEither (fmap Right)
    
abstractLocal
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) m (VarName p a b)
abstractLocal ns
  = abstract
      (\case
      Right (Left (Local n))
       -> Local <$> elemIndex (Just n) ns
      
      _
       -> Nothing)

-- | Marker type for source-external references
newtype Import a = Import { getImport :: a }
