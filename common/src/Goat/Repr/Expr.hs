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
import Control.Applicative (Const(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.Bifunctor (Bifunctor(..))
import Data.Bifunctor.Wrapped (WrappedBifunctor(..))
import Data.Bifoldable (Bifoldable)
import Data.Bitraversable
  (Bitraversable(..), bisequenceA)
import Data.Discrimination
  ( Grouping(..), runGroup, nubWith, nub
  , Sorting(..), toMapWith
  )
import Data.Functor (($>))
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
import Data.Semigroup (Semigroup(..))
import Data.String (IsString(..))
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
 :: ( Eq k, Sorting k, Functor (r k)
    , MonadBlock
        (Block (AnnCpts [View (Trail k)]) k) m
    )
 => Bindings
      (Assocs (,) (ShadowDecls (m k)) (Trail k))
      (AnnCpts [Trail k] k)
      m
      (VarName k k a)
 -> Bindings
      (AnnDefns [View (Trail k)] [Trail k] r k)
      (AnnDefns [View (Trail k)] [Trail k] r k)
      (Scope (Super Int) (Scope (Public k) m))
      (VarName k b a)
abstractBindings bviews = toAbs bparts
  where
  ns
    = getConst
        (transverseBindings
          (Const . getNames) bviews)
  bdefns = abstractVars ns . return <$> bviews
  env = Define (return . return . localVar <$> ns)
  bparts
    = embedBindings
        componentsFromViews
        (liftBindings2
          Parts
          (transPattern
            matchDefn
            (hoistBindings (lift . lift) bdefns))
          env)
  
  getNames
   :: Assocs (,) f (Trail b) c -> [b]
  getNames (Assocs pairs) = [n | (n:|_,_) <- pairs]
  
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
  
  {-
  captureComponents
   :: MonadBlock (Block (AnnCpts [a] k)) m
   => Cpts a
   -> ([Maybe Ident], m (VarName b Ident c))
  captureComponents (Assocs kv)
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
            (Block (Extend kv Nothing))
  -}

componentsFromViews
 :: ( Sorting k
    , Functor (r k)
    , MonadBlock
        (Block (AnnCpts [View (Trail k)]) k) m
    )
 => Parts (ShadowCpts (m k) (Trail k)) [] a
 -> Bindings
      (Parts
        (AnnDefns [View (Trail k)] b r k)
        (AnnDefns [View (Trail k)] b r k))
      (AnnDefns [View (Trail k)] b r k)
      (Scope (Super Int) (Scope (Public k) m))
      a
componentsFromViews (Parts (Assocs pairs) as)
  = transPattern
      declareDefn
      (Index
        (embedBindings
          componentsWrap
          (liftBindings2
            Parts
            bs
            (Define (map return as)))))
  where
  bs
    = foldMapWithIndex
        (\ i f -> f i)
        (componentsFromNode crumbps)
  
  componentsWrap
   :: ( Sorting k
      , MonadBlock (Block (AnnCpts [t]) k) m
      , MonadBlock (Block (AnnCpts [u]) k) m
      )
   => Parts
        (Parts
          (Assocs ((,,) [t])
            (Tag
              (Compose
                (AnnCpts [t] k)
                (Scope (Super Int)
                  (Scope (Public k) m)))
              Identity)
            k)
          (Parts
            (Assocs' (,) k)
            (Assocs ((,,) [u])
              (Tag
                (Compose
                  (AnnCpts [u] k)
                  (Scope (Super Int)
                    (Scope (Public k) m)))
                Identity)
              k)))
        []
        a
   -> Bindings
        (Parts
          (AnnCpts [t] k)
          (Parts
            (AnnDefns [v] b r k)
            (AnnDefns [u] b r k)))
        p
        (Scope (Local Int)
          (Scope (Super Int) (Scope (Public k) m)))
        a
  componentsWrap
    (Parts (Parts ascs (Parts lascs pascs)) as)
    = Define (Parts cpts (Parts lcpts pcpts))
    where
    cpts
      = zipWrapAssocs
          (lift . lift . lift ... wrapTag) as ascs
    lcpts
      = declareDefn
          (componentsFromAssocs
            (\ (n, Identity a)
             -> (n, ([], return a)))
            lascs)
    pcpts
      = declareDefn
          (mapWrapAssocs wrapPublic pascs)
    
    wrapPublic
     :: MonadBlock (Block (AnnCpts [t]) k) m
     => Int
     -> Tag
          (Compose
            (AnnCpts [t] k)
            (Scope (Super Int) (Scope (Public k) m)))
          Identity
          a
     -> Scope b
          (Scope (Super Int) (Scope (Public k) m)) a
    wrapPublic i tag
      = lift
          (Scope
            (lift 
              (wrapTag
                (B (Super i)) (F . return <$> tag))))
  
  crumbps
    = zipWith
        (\ i (t, a)
         -> let
            vt = case a of
                 Tag (Left (Local{}))
                  -> Tag (Left (Local t))
                 
                 Tag (Right (ShadowPublic{}))
                  -> Tag (Right (Public t))
            in
            case t of
            n:|[]
             -> ((n, Just i), (pure n, vt, a))
            
            n:|n':ns
             -> ((n, Nothing), (n':|ns, vt, a)))
        [0..]
        pairs

zipWrapAssocs
 :: Sorting k
 => (a -> f b -> c)
 -> [a]
 -> Assocs ((,,) [u]) f k b
 -> AnnCpts [u] k c
zipWrapAssocs wrap as (Assocs tups)
  = componentsFromAssocs
      (\ (ts, a, Identity c) -> (a, (ts, c)))
      (Assocs
        (zipWith
          (\ a tup -> second (pure . wrap a) tup)
          as
          tups))

componentsFromAssocs
 :: Sorting a
 => (p a (f b) -> (a, g c))
 -> Assocs p f a b -> Components g a c
componentsFromAssocs f (Assocs ps)
  = Components
      (toMapWith (<>) (map (fmap pure . f) ps))

mapWrapAssocs
 :: Sorting k
 => (Int -> f a -> b)
 -> Assocs ((,,) [u]) f k a
 -> AnnCpts [u] k b
mapWrapAssocs wrap asc
  = case
    componentsFromAssocs
      (\ (ts, a, b) -> (a, (ts, b))) asc
    of
    Components kv
     -> Components
          (mapWithIndex (fmap . fmap . wrap) kv)
          
wrapTag
 :: MonadBlock (Block (AnnCpts [t]) k) m
 => a
 -> Tag
      (Compose
        (AnnCpts [t] k)
        (Scope (Super Int) (Scope (Public k) m)))
      Identity
      a
 -> m a
wrapTag a (Tag (Left (Compose cpts)))
  = wrapBlock (Block (Extend cpts (return a)))
wrapTag _ (Tag (Right (Identity a))) = return a

componentsFromNode
 :: ( Sorting k
    , MonadBlock (Block (AnnCpts [t]) k) m
    , MonadBlock (Block (AnnCpts [u]) k) m
    )
 => [ ( (k, Maybe Int)
      , (NonEmpty k, t, ShadowDecls (m k) a)
      )
    ]
 -> Map k
      ( Int 
         -> Bindings
              (Parts
                (Assocs ((,,) [t])
                  (Tag
                    (Compose
                      (AnnCpts [t] k)
                      (Scope (Super Int)
                        (Scope (Public k) m)))
                    Identity)
                  k)
                (Parts
                  (Assocs' (,) k)
                  (Assocs ((,,) [u]) 
                    (Tag 
                      (Compose
                        (AnnCpts [u] k)
                        (Scope (Super Int)
                          (Scope (Public k) m)))
                      Identity)
                    k)))
              (AnnCpts [t] k)
              (Scope (Local Int)
                (Scope
                  (Super Int) (Scope (Public k) m)))
              a
      )
componentsFromNode crumbps
  = toMapWith (<>)
      (zipWith
        (componentsFromGroup . fst)
        (nubWith fst crumbps)
        (runGroup grouping crumbps)
       >>= id)

componentsFromGroup
 :: ( Sorting k
    , MonadBlock (Block (AnnCpts [t]) k) m
    , MonadBlock (Block (AnnCpts [u]) k) m
    )
 => (k, Maybe b)
 -> [(NonEmpty k, t, ShadowDecls (m k) a)]
 -> [ ( k
      , Int
         -> Bindings
              (Parts
                (Assocs ((,,) [t])
                  (Tag 
                    (Compose
                      (AnnCpts [t] k)
                      (Scope (Super Int)
                        (Scope (Public k) m)))
                    Identity)
                  k)
                (Parts
                  (Assocs' (,) k)
                  (Assocs ((,,) [u]) 
                    (Tag 
                      (Compose 
                        (AnnCpts [u] k)
                        (Scope (Super Int)
                          (Scope (Public k) m)))
                      Identity)
                    k)))
              (AnnCpts [t] k)
              (Scope
                (Local Int)
                (Scope
                  (Super Int) (Scope (Public k) m)))
              a
      )
    ]
componentsFromGroup (n, Just _) tups
  = map
      (\ case 
      (_, t, Tag (Left (Local a)))
       -> ( n
          , \ i
             -> Define
                  (Parts
                    (asingr ([t], n, return a))
                    (Parts
                      (asing (n, bind i))
                      mempty))
          )
      
      (_, t, Tag (Right (ShadowPublic m a)))
       -> let
          sm = lift (lift (Scope (B . Public <$> m)))
          in
          ( n
          , \ i
             -> Define
                  (Parts
                    (asingr ([t], n, return a))
                    (Parts
                      (asing (n, sm))
                      (asingr ([], n, bind i))))
          ))
      tups
  where
  asing pab = Assocs [second pure pab]
  asingr pab
    = Assocs [second (Tag . Right . pure) pab]
  bind i = Scope (return (B (Local i)))
  
componentsFromGroup (n, Nothing) tups = [(n, f)]
  where
  f i
    = Index
        (embedBindings (componentsWrap ts n i) bs)
  bs =
    getConst
        (traverseWithIndex
          (\ i f
           -> Const
              (hoistBindings 
                (hoistScope lift)
                (f i)))
          (componentsFromNode crumbps))
  
  componentsWrap
   :: ( Sorting k
      , MonadBlock (Block (AnnCpts [t]) k) m
      , MonadBlock (Block (AnnCpts [u]) k) m
      )
   => [t]
   -> k
   -> Int
   -> Parts
        (Assocs ((,,) [t])
          (Tag
            (Compose
              (AnnCpts [t] k)
              (Scope
                (Super Int) (Scope (Public k) m)))
            Identity)
          k)
        (Parts
          (Assocs' (,) k)
          (Assocs ((,,) [u])
            (Tag
              (Compose
                (AnnCpts [u] k)
                (Scope
                  (Super Int) (Scope (Public k) m)))
              Identity)
            k))
        a
   -> Bindings
        (Parts
          (AnnCpts [t] k)
          (Parts
            (Assocs ((,,) [t])
              (Tag
                (Compose
                  (AnnCpts [t] k)
                  (Scope (Super Int)
                    (Scope (Public k) m)))
                Identity)
              k)
            (Parts
              (Assocs' (,) k)
              (Assocs ((,,) [u])
                (Tag
                  (Compose
                    (AnnCpts [u] k)
                    (Scope (Super Int)
                      (Scope (Public k) m)))
                  Identity)
                k))))
        (AnnCpts [t] k)
        (Scope (Local Int)
          (Scope (Local Int) 
            (Scope
              (Super Int) (Scope (Public k) m))))
        a
  componentsWrap
    ts n i (Parts ascs (Parts lascs pascs))
    = Define
        (Parts
          cpts
          (Parts ascs' (Parts lascs' pascs')))
    where
    cpts = mapWrapAssocs wrapPattern ascs 
    lcpts
      = componentsFromAssocs 
          (\ (n, Identity a)
           -> (n, ([], return (return a))))
          lascs
    pcpts = mapWrapAssocs wrapPublic pascs
    
    ascs' = asingfl (ts, n, Compose lcpts)
    lascs' = asing (n, bind i)
    pascs' = asingfl ([], n, Compose pcpts)
    
    asing pab = Assocs [second pure pab]
    asingfl pafb = Assocs [second (Tag . Left) pafb]
    bind i = Scope (return (B (Local i)))

  
  wrapPublic
   :: ( MonadBlock (Block (AnnCpts [t]) k) m
      , Monad n
      )
   => Int
   -> Tag
        (Compose
          (AnnCpts [t] k)
          (Scope (Super Int) (Scope (Public k) m)))
        Identity
        a
   -> Scope (Super Int) (Scope b m) (n a)
  wrapPublic i tag
    = Scope
        (lift 
          (wrapTag
            (B (Super i))
            (F . return . return <$> tag)))
          
  wrapPattern
   :: MonadBlock (Block (AnnCpts [t]) k) m
   => Int
   -> Tag
        (Compose
          (AnnCpts [t] k)
          (Scope (Super Int) (Scope (Public k) m)))
        Identity
        a
   -> Scope b
        (Scope (Local Int) (Scope c (Scope d m)))
        a
  wrapPattern i tag
    = lift
        (Scope
          (lift
            (lift 
              (wrapTag
                (B (Local i))
                (F . return <$> tag)))))
  
  (ts, crumbps)
    = traverseWithIndex
        (\ i (k:|ks, t, a)
         -> ( [t]
            , case ks of
              []
               -> ((k, Just i), (pure k, t, a))
              
              k':ks
               -> ((k, Nothing), (k':|ks, t, a))
            ))
        tups
      


{-
componentsBlockFromDeclares
 :: (Grouping k, MonadBlock (Block (TagCpts k)) m)
 => Assocs (,) [VarTrail k] a
 -> ( Cpts g ()
    , Bindings 
        (Parts (Cpts g) (Cpts g))
        p
        (Scope (Local Int) (Scope (Super Ident) m))
        a
    )
componentsBlockFromDeclares (Assocs ps)
  = (lp, Define (Parts lc pc))
  where
  -- public inner scope
  pc
    = lift
   <$> reprFromNode
        (iterPaths reprFromNode . k <$> pr)
  
  -- local outer scope
  lc
    = localReprFromNode
        lr
        (iterPaths reprFromNode . k)
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

-- | 'reprFromPathsWith kp asgs i' generates a value from set of assigns 'asgs'.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
reprFromPathsWith
 :: Semigroup m
 => (Map Text m -> Ident -> m)
 -> Paths (Map Text) (Ident -> m)
 -> Ident -> m
reprFromPathsWith kp asgs n
  = merge n
      (iterPaths
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
-}


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
