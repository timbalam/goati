{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, TypeFamilies, RankNTypes, LambdaCase, FlexibleInstances, ScopedTypeVariables #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang.Class'.
module Goat.Repr.Expr
  ( module Goat.Repr.Expr
  , Scope(..), Var(..), Ident, Block, AnnCpts
  ) where

import Goat.Repr.Pattern
import Goat.Util (abstractEither, (<&>), (...))
import Control.Applicative (liftA2, Const(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.Bifunctor (Bifunctor(..))
import Data.Bifunctor.Wrapped (WrappedBifunctor(..))
import Data.Bifoldable (Bifoldable)
import Data.Bitraversable
  (Bitraversable(..), bisequenceA)
import Data.Discrimination
  ( Grouping(..), runGroup, nubWith, nub
  , Sorting(..), toMapWith, toMap
  )
import Data.Foldable (foldl')
import Data.Functor (($>))
import Data.Functor.Alt (Alt(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.These (mergeTheseWith, these, These(..))
import Data.List (elemIndex)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Traversable (fmapDefault, foldMapDefault)
import Data.Semigroup
  (Semigroup(..), First(..), All(..))
import Data.String (IsString(..))
import Data.Void (Void)
import Bound (Scope(..), Var(..), Bound(..))
import Bound.Scope
  (hoistScope, bitransverseScope, abstract)

import Debug.Trace
  

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
  ( Functor f, Functor g, Functor (r Ident)
  , MeasureExpr (Defns f g r Ident) v
  )
   => MonadBlock
        (Block (Components f) Ident)
        (Repr (Defns f g r Ident) v)
  where
  wrapBlock (Block (Extend c m))
    = Repr
        (Comp
          (memo
            (Ext (Define (declareDefn c)) m)))
    where

-- |
data Expr f m a
  = Ext
      (Bindings f f
        (Scope (Super Int)
          (Scope (Public Ident) m))
        a)
      (m a)
  | Sel (m a) Ident
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

newtype Declares f a = Declares (f a)
  deriving (Functor, Foldable, Traversable)

newtype Matches f a = Matches (f a)
  deriving (Functor, Foldable, Traversable)

type Defns f g r a =
  Tag
    (Tag 
      (Declares (Components f a))
      (Matches (Components g a)))
    (r a)

declareDefn = Tag . Left . Tag . Left . Declares
matchDefn = Tag . Left . Tag . Right . Matches
otherDefn = Tag . Right

type AnnDefns a b r k
  = Defns ((,) a) ((,) b) r k

type VarName a b
  = Either (Either (Local a) (Public b))

localVar = Left . Left . Local
publicVar = Left . Right . Public
otherVar = Right

abstractBindings
 :: ( Ord k, Sorting k, Functor (r k)
    , MonadBlock
        (Block (AnnCpts [View (Trail k)]) k) m
    -- debug
    , Show k
    )
 => Bindings
      (AssocShadows (m k) (Trail k))
      (AnnCpts [Trail k] k)
      m
      (VarName k k a)
 -> Bindings
      (AnnDefns [View (Trail k)] [Trail k] r k)
      (AnnDefns [View (Trail k)] [Trail k] r k)
      (Scope (Super Int) (Scope (Public k) m))
      (VarName k b a)
abstractBindings bs = toAbs bsdefns
  where
  bsabs
    = abstractVars (Map.keys env) . return
   <$> hoistBindings (lift . lift) bs
  bscpts
    = squashBindings
        (liftBindings2
          (transPattern declareDefn 
           ... componentsFromViews)
          (transPattern matchDefn bsabs)
          (Define env))
  
  env
    = getConst
        (transverseBindings
          (\ (Assocs ps)
           -> Const 
                (toMap
                  (map
                    (\ (n:|_, _)
                     -> (n, bindLocal n))
                    ps)))
          bs)
  (_env, bsdefns)
    = transverseBindings
        (\ (Parts fa@(Components kv) ga)
         -> ( ()
            --Map.mapWithKey (const . bindLocal) kv
            , Parts
                (declareDefn fa) (declareDefn ga)
            ))
        bscpts
  
  bindLocal
   :: (Monad m, Monad n)
   => k -> m (n (VarName k a b))
  bindLocal = return . return . localVar
  
   -- bind abstracted local variables to pattern returned by 
   -- 'componentsFromViews'
  toAbs
   :: (Functor p, Functor f, Monad m)
   => Bindings (Parts p f) p
        (Scope (Super Int) (Scope (Public k) m))
        (Scope (Local Int)
          (Scope (Public k) m) a)
   -> Bindings f p
        (Scope (Super Int)
          (Scope (Public k) m))
        a
  toAbs bs
    = Index
        (hoistBindings lift bs
         >>>= hoistScope lift)

componentsFromViews
 :: ( Ord k, Sorting k
    , MonadBlock
        (Block (AnnCpts [View (Trail k)]) k) m
   -- debug
    , Show k
    )
 => AssocShadows (m k) (Trail k) a
 -> Map k a
 -> Bindings
      (Parts
        (AnnCpts [View (Trail k)] k)
        (AnnCpts [View (Trail k)] k))
      p
      (Scope (Super Int) (Scope (Public k) m))
      a
componentsFromViews (Assocs pairs) kva
  = Define
      (uncurry
        (zipWrapComponentSplit kva lpts ppts)
        (componentSplitFromNode crumbps))
  where
  lpts = toMapWith (flip (<>)) <$> lkts
  ppts = toMapWith (flip (<>)) <$> pkts
  (lkts, pkts, crumbps)
    = foldMapWithIndex
        (\ i (t, a)
         -> let
            (vt, pvt)
              = case a of
                Tag (Left (Local{}))
                 -> (Tag (Left (Local t)), mempty)
                
                Tag (Right (ShadowPublic{}))
                 -> let
                    vt = Tag (Right (Public t))
                    in
                    (vt, Public [(n, vt)])
            in
            case t of
            n:|[]
             -> ( Local [(n,vt)]
                , pvt
                , [((n, Just i), (pure n, vt, a))]
                )
            
            n:|n':ns
             -> ( Local [(n,vt)]
                , pvt
                , [((n, Nothing), (n':|ns, vt, a))]
                ))
        pairs
  
zipWrapComponentSplit
 :: ( Ord k, Sorting k
    , Functor (f k), MonadBlock (Block f k) m
    )
 => Map k a
 -> Local (Map k [t])
 -> Public (Map k [t])
 -> Local
      ( All
      , Map k
          (NonEmpty
            ( Bool
            , Either
                (f k
                  (Scope
                    (Super Int)
                    (Scope (Public k) m)
                    a))
                (Either (m k) a)
            ))
      )
 -> Public
      (Map k
        (NonEmpty
          (Either
            (f k
              (Scope
                (Super Int)
                (Scope (Public k) m)
                a))
            a)))
 -> Parts
      (AnnCpts [t] k)
      (AnnCpts [t] k)
      (Scope (Super Int) (Scope (Public k) m) a)
zipWrapComponentSplit kva lpts ppts lbkv pkv
  = Parts lcpts pcpts
  where
  Local lcpts
    = liftA2 (zipWrapLocal kva) lpts lbkv
  Public pcpts
    = liftA2 wrapPublic ppts pkv
    
  zipWrapLocal kva pts
    = Components
    . Map.intersectionWith
        (,)
        pts
    . Map.intersectionWith
        (\ a p
         -> fmap (localComponentWith a)
          . collectWhen <$> p)
        kva
    . snd
  
  wrapPublic pts
    = Components
    . Map.intersectionWith
        (,)
        pts
    . mapWithIndex
        (fmap . fmap . publicComponent)

localComponentWith
 :: MonadBlock (Block f k) m
 => a
 -> Either
      (f k
        (Scope (Super Int) (Scope (Public k) m) a))
      (Either (m k) a)
 -> Scope (Super Int) (Scope (Public k) m) a
localComponentWith a
  = either (wrap a)
      (either
        (lift . Scope . fmap (B . Public))
        return)
  where
  wrap a f
    = lift (lift (wrapExtend f (return a)))

wrapExtend
 :: MonadBlock (Block f k) m
 => f k (Scope (Super Int) (Scope (Public k) m) a)
 -> m a
 -> m a
wrapExtend bs m
  = wrapBlock (Block (Extend bs m))

componentSplitFromNode
 :: ( Sorting k
    , MonadBlock (Block (AnnCpts [t]) k) m
     -- debug
    , Show k
    )
 => [ ( (k, Maybe Int)
      , (NonEmpty k, t, ShadowView (m k) a)
      ) ]
 -> ( Local
        ( All
        , Map k
            (NonEmpty
              ( Bool
              , Either
                  (AnnCpts [t] k
                    (Scope (Super Int)
                      (Scope (Public k) m) a))
                  (Either (m k) a)
              ))
        )
    , Public
        (Map k
          (NonEmpty
            (Either
              (AnnCpts [t] k
                (Scope (Super Int)
                  (Scope (Public k) m) a))
              a)))
    )
componentSplitFromNode crumbps
  = ( second assocsToComponents <$> lbasc
    , assocsToComponents <$> pasc
    )
  where
  (lp, pasc)
    = foldMap id
        (zipWith
          (uncurry componentSplitFromGroup . fst)
          (nubWith fst crumbps)
          (runGroup grouping crumbps))
  
  assocsToComponents
   :: Sorting k
   => Table (,) NonEmpty k a
   -> Components f k a
  assocsToComponents (Assocs tups)
    = Components
        (toMapWith (flip (<>)) tups)


componentSplitFromGroup
 :: ( Sorting k
    , MonadBlock (Block (AnnCpts [t]) k) m
     -- debug
    , Show k, Show b
    )
 => k
 -> Maybe b
 -> [(NonEmpty k, t, ShadowView (m k) a)]
 -> ( Local
        ( All
        , Table (,) NonEmpty k
            ( Bool
            , Either 
                (AnnCpts [t] k
                  (Scope
                    (Super Int)
                    (Scope (Public k) m)
                    a))
                (Either (m k) a)
            )
        )
    , Public
        (Table (,) NonEmpty k
          (Either
            (AnnCpts [t] k
              (Scope
                (Super Int)
                (Scope (Public k) m)
                a))
            a))
    )
componentSplitFromGroup n (Just _) tups
  = foldMap
      (\ (_, _, tag) -> splitShadowView n tag)
      tups
  where
  splitShadowView
   :: k
   -> ShadowView b a
   -> ( Local
          ( All
          , Table (,) NonEmpty k
              (Bool, Either c (Either b a))
          )
      , Public
          (Table (,) NonEmpty k (Either c a))
      )
  splitShadowView n (Tag (Left (Local a)))
    = ( Local
          ( All False
          , Assocs
              [(n, pure (False, Right (Right a)))]
          )
      , mempty
      )
  
  splitShadowView n (Tag (Right (ShadowPublic m a)))
    = ( Local
          ( All True
          , Assocs
              [(n, pure (True, Right (Left m)))]
          )
      , Public (Assocs [(n, pure (Right a))])
      )

componentSplitFromGroup n Nothing tups
  = uncurry
      (wrapComponentSplit n lts pts)
      (componentSplitFromNode crumbps)
  where
  lpts = toMapWith (flip (<>)) <$> lkts
  ppts = toMapWith (flip (<>)) <$> pkts
  ((lkts, pkts), crumbps)
    = foldMapWithIndex
        (\ i (k:|ks, t, a)
         -> ( ( Local [(k,[t])]
              , case a of
                Tag (Left (Local{})) -> mempty
                _ -> Public [(k, [t])]
              )
            , case ks of
              []
               -> ((k, Just i), (pure k, t, a))
              
              k':ks
               -> ((k, Nothing), (k':|ks, t, a))
            ))
        tups
  
wrapComponentSplit
 :: ( Sorting k, Functor (f k)
    , MonadBlock (Block f k) m
    )
 => k
 -> Local (Map k [t])
 -> Public (Map k [t]) 
 -> Local 
      ( All
      , Map k
          (NonEmpty
            ( Bool
            , Either
                (f k
                  (Scope (Super Int)
                    (Scope (Public k) m) a))
                (Either (m k) a)
            ))
      )
 -> Public
      (Map k
        (NonEmpty
          (Either
            (f k
              (Scope (Super Int)
                (Scope (Public k) m) a))
            a)))
 -> ( Local
        ( All
        , Table (,) NonEmpty k
            ( Bool
            , Either
                (AnnCpts [t] k
                  (Scope
                    (Super Int)
                    (Scope (Public k) m)
                    a))
                (Either (m k) a)
            )
        )
    , Public
        (Table (,) NonEmpty k
          (Either
            (AnnCpts [t] k
              (Scope
                (Super Int)
                (Scope (Public k) m)
                a))
            a))
    )
wrapComponentSplit n lpts ppts lbkv pkv
  = ( liftA2
        (\ pts (All b, kv)
         -> ( All b
            , Assocs
                [ ( n
                  , pure
                    (b, Left (wrapLocal pts kv))
                  ) ]
            ))
        lpts
        lbkv
    , liftA2
        (\ pts kv
         -> if Map.null kv then
            mempty
            else
            Assocs
              [ ( n
                , pure (Left (wrapPublic pts kv))
                ) ])
        ppts
        pkv
    )
  where
  wrapLocal pts
    = Components
    . Map.intersectionWith (,) pts
    . mapWithIndex
        (\ i p
         -> fmap (localComponent i)
          . collectWhen <$> p)
  
  wrapPublic pts
    = Components
    . Map.intersectionWith
        (,)
        pts
    . mapWithIndex
        (fmap . fmap . publicComponent)

collectWhen
 :: Semigroup m
 => NonEmpty (Bool, m) -> NonEmpty m
collectWhen ne
  = NonEmpty.fromList ps
  where
  bps = NonEmpty.toList ne
  ps
    = join
        (zipWith
          (collectIf . fst)
          (nubWith fst bps)
          (runGroup grouping bps))
    
  collectIf True [] = []
  collectIf True (p:ps) = [foldl' (<>) p ps]
  collectIf False ps = ps

localComponent
 :: (Functor (f k), MonadBlock (Block f k) m)
 => Int
 -> Either
      (f k 
        (Scope (Super Int) (Scope (Public k) m) a))
      (Either (m k) a)
 -> Scope (Super Int) (Scope (Public k) m) a
localComponent i 
  = either
      (wrap i)
      (either
        (lift . Scope . fmap (B . Public))
        return)
  where
  wrap i f
    = Scope
        (lift
          (wrapExtend
            (fmap (F . return) <$> f)
            (return (B (Super i)))))

publicComponent
 :: (Functor (f k), MonadBlock (Block f k) m)
 => Int
 -> Either
      (f k
        (Scope (Super Int) (Scope (Public k) m) a))
      a
 -> Scope (Super Int) (Scope (Public k) m) a
publicComponent i
  = either (wrap i) return
  where
  wrap i f
    = Scope
        (lift
          (wrapExtend
            (fmap (F . return) <$> f)
            (return (B (Super i)))))
  
-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVars
 :: (Monad m, Eq a)
 => [a]
 -> m (VarName a b c)
 -> Scope (Local Int)
      (Scope (Public b) m) (VarName a b' c)
abstractVars ns m
  = abstractLocal ns (abstractPublic m)
  where
  abstractPublic
    = abstractEither
        (\case
        Left (Left a) -> Right (Left (Left a))
        Left (Right b) -> Left b
        Right c -> Right (Right c))
    
abstractLocal
 :: (Monad m, Eq a)
 => [a]
 -> m (VarName a b c)
 -> Scope (Local Int) m (VarName a b c)
abstractLocal ns
  = abstract
      (\case
      Left (Left (Local n))
       -> Local <$> elemIndex n ns
      
      _
       -> Nothing)

-- | Marker type for source-external references
newtype Import a = Import { getImport :: a }
