{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Goat.Repr.Eval.Dyn
  ( module Goat.Repr.Eval.Dyn
  , DynCpts(..), Void, Measure(..)
  )
where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Dyn
import Goat.Repr.Preface
import Goat.Lang.Error
  ( TypeError(..), displayTypeError
  , DefnError(..), displayDefnError
  , ScopeError(..), displayScopeError
  , ImportError(..), displayImportError
  )
import Goat.Util ((<&>), (...), withoutKeys)
import Control.Applicative (liftA2)
import Control.Monad (ap, join)
import Control.Monad.Trans (lift)
import Data.Align (align)
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
import Data.Function (on)
import Data.Functor (($>))
import Data.List (intersperse)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Semigroup ((<>))
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Text as Text
import Data.These (These(..))
import Data.Void (Void)
import Bound (instantiate, (>>>=))
import Prelude.Extras (Eq1(..), Show1(..))

--import Debug.Trace


-- | Unrolled expression
data Eval f
  = Eval
      (Value (f (Repr f (Eval f) Void)))

bindHoles
 :: MeasureExpr (DynCpts e) v
 => (TypeError -> e)
 -> Expr (DynCpts e) (Repr (DynCpts e) v) a
 -> Expr (DynCpts e) (Repr (DynCpts e) v) Void
bindHoles throwe f
  = f >>>= \_ -> throwRepr (throwe Hole)

type MemoRepr 
  = Repr (DynCpts DynError) (Eval (DynCpts DynError))

instance
  MeasureExpr
    (DynCpts DynError) (Eval (DynCpts DynError)) 
  where
  measureExpr f
    = Eval (eval TypeError (bindHoles TypeError f))

instance
  Measure
    (Memo f (Eval (DynCpts DynError)))
    (Value
      (DynCpts DynError
        (Repr (DynCpts DynError)
          (Eval (DynCpts DynError))
          Void)))
  where
  measure (Memo (Eval v) _) = v

instance
  Measure
    (Memo 
      (Expr (DynCpts (DynError))
        (Repr (DynCpts DynError) ()))
      ())
    (Value 
      (DynCpts DynError
        (Repr (DynCpts DynError) () Void)))
  where
  measure (Memo _ f)
    = eval TypeError (bindHoles TypeError f)

decompose
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> DynCpts e ()
 -> Repr (DynCpts e) v Void
 -> [Repr (DynCpts e) v Void]
decompose throwe ~(DynCpts kp mep) m = ms
  where
  DynCpts km mem
    = valueComponents throwe (measureRepr m)
  
  kmbind
    = Map.mapMaybeWithKey
        (\ n th
         -> split
              (fromMaybe
                (throwe
                  (NotComponent (Text.unpack n)))
                mem)
              th)
        (align kp km)
  
  mrem
    = getRemaining throwe (Map.keysSet kp) m
  
  ms
    = bifoldMap
        (pure . either throwRepr id)
        pure
        (Extend kmbind (maybe mrem throwRepr mep))
  
  split
   :: e
   -> These (Either e ()) (Either e v)
   -> Maybe (Either e v)
  split e (This _) = Just (Left e)
  split _e (That _) = Nothing
  split _e (These ep ev) = Just (ep >> ev)
  
  select
   :: MeasureExpr (DynCpts e) v
   => Either e (Repr (DynCpts e) v a)
   -> Repr (DynCpts e) v a
  select = either throwRepr id

throwRepr
 :: MeasureExpr (DynCpts e) v
 => e -> Repr (DynCpts e) v a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure (Expr f (Repr f v)) v
 => f (Scope (Super Ident)
        (Scope (Public Ident) (Repr f v)) a)
 -> Repr f v a
wrapComponents c
  = Repr (Comp (memo (Ext (Define c) emptyRepr)))

getRemaining
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Set Text
 -> Repr (DynCpts e) v Void
 -> Repr (DynCpts e) v Void
getRemaining throwe ks (Repr v)
  = either
      throwRepr
      (\ v -> Repr (v >>= fmap (memo . (`id` ks))))
      (traverse
        (simplify throwe deleteExt . unmemo)
        v)
  where
  deleteExt bs ev
    = pure
        (Comp
          (deleteComponents bs
            (\ ks
             -> either
                  throwRepr
                  (Repr . fmap (memo . (`id` ks)))
                  ev)))
    

deleteComponents
 :: Bindings (DynCpts e) (DynCpts e)
      (Scope (Super Ident)
        (Scope (Public Ident)
          (Repr (DynCpts e) v)))
      a
 -> (Set Text -> Repr (DynCpts e) v a)
 -> Set Text
 -> Expr (DynCpts e) (Repr (DynCpts e) v) a
deleteComponents bs f ks = Ext bs' (f ks')
  where
    (ks', bs')
      = transverseBindings
          (\ (DynCpts km me)
           -> ( maybe
                  (ks
                   `Set.difference` Map.keysSet km)
                  (\_ -> Set.empty)
                  me
              , DynCpts (km `withoutKeys` ks) me
              ))
          bs

getDyn
 :: forall e v a
  . MeasureExpr (DynCpts e) v
 => (TypeError -> e)
 -> DynCpts e (Repr (DynCpts e) v a)
 -> Ident
 -> Repr (DynCpts e) v a
getDyn throwe ~(DynCpts km me) = get
  where
  get :: Ident -> Repr (DynCpts e) v a
  get n
    = Map.findWithDefault
        (err n)
        n
        (either throwRepr id <$> km)
    
  err
   :: Ident -> Repr (DynCpts e) v a
  err n
    = throwRepr
        (fromMaybe
          (throwe (NotComponent (Text.unpack n)))
          me)

eval
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Expr (DynCpts e) (Repr (DynCpts e) v) Void
 -> Value (DynCpts e (Repr (DynCpts e) v Void))
eval throwe f = v'
  where
  v'
    = either
        (Comp . throwDyn)
        (fmap (fmap (memoSimplify throwe)))
        (simplify throwe evalExt f)
  
  subst
    = instantiate 
        (\ (Public n)
         -> getDyn
              throwe (valueComponents throwe v') n)
  
  evalExt bs ev
    = pure
        (Comp
          (substituteExt throwe subst bs
            (either
                throwDyn
                (valueComponents throwe)
                ev)))

substituteExt
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
     -- debug
    , Show e
    )
 => (TypeError -> e)
 -> (Scope (Public Ident) (Repr (DynCpts e) v) Void
     -> Repr (DynCpts e) v Void)
 -> Bindings
      (DynCpts e) (DynCpts e)
      (Scope (Super Ident)
        (Scope (Public Ident) (Repr (DynCpts e) v)))
      Void
 -> DynCpts e (Repr (DynCpts e) v Void)
 -> DynCpts e (Repr (DynCpts e) v Void)
substituteExt throwe subst bs c
  = extendComponents c' c
  where
  c'
    = subst . substSuper
   <$> substituteBindings
        (\ p v
         -> map
              (lift . lift)
              (decompose throwe p
                (subst (substSuper v))))
        bs
  
  substSuper
    = instantiate
        (\ (Super n) -> lift (getDyn throwe c n))

extendComponents
 :: DynCpts e a -> DynCpts e a -> DynCpts e a
extendComponents
  (DynCpts km Nothing) (DynCpts nkm nmem)
  = DynCpts (Map.union km nkm) nmem
extendComponents c _ = c

memoSimplify
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Repr (DynCpts e) v Void
 -> Repr (DynCpts e) v Void
memoSimplify throwe ~(Repr v)
  = either
      throwRepr
      (Repr . join)
      (traverse (simplify throwe memoExt . unmemo) v)
  where
  memoExt bs ev
    = pure
        (Comp
          (memo
            (Ext bs
              (either throwRepr Repr ev))))

simplify
 :: forall e f v a
  . ( MeasureExpr f v
    , Measure
        (Memo
          (Expr f (Repr f v)) v)
        (Value (DynCpts e (Repr f v Void)))
    -- debug
    , Traversable f, Show1 f, Show e
    )
 => (TypeError -> e)
 -> (Bindings
      f f
      (Scope (Super Ident)
        (Scope (Public Ident) (Repr f v)))
      Void
     -> Either e (Value a)
     -> Either e (Value a))
 -> Expr f (Repr f v) Void
 -> Either e (Value a)
simplify throwe simplifyExt = go
  where
  go
    = \case
      Ext bs ~(Repr v) 
       -> simplifyExt bs
            (traverse (go . unmemo) v <&> join)

      Sel m n
       -> let
          DynCpts km me
            = valueComponents throwe (measureRepr m)
          err
            = fromMaybe
                (throwe
                  (NotComponent (Text.unpack n)))
                me
          in
          case
          Map.findWithDefault (Left err) n km
          of
          Left e
           -> Left e
          
          Right ~(Repr v)
           -> traverse (go . unmemo) v <&> join
      
      Add a b -> num2num2num (+) a b
      Sub a b -> num2num2num (-) a b
      Mul a b -> num2num2num (*) a b
      Div a b -> num2num2num (/) a b
      Pow a b -> num2num2num (**) a b
      Eq a b  -> num2num2bool (==) a b
      Ne a b  -> num2num2bool (/=) a b
      Lt a b  -> num2num2bool (<) a b
      Le a b  -> num2num2bool (<=) a b
      Gt a b  -> num2num2bool (>) a b
      Ge a b  -> num2num2bool (>=) a b
      Or a b  -> bool2bool2bool (||) a b
      And a b -> bool2bool2bool (&&) a b
      Not a   -> bool2bool not a
      Neg a   -> num2num negate a

  binary
   :: forall f a b c d
    . Applicative f
   => (a -> f b)
   -> (f d -> c)
   -> (b -> b -> d)
   -> a -> a -> c
  binary ina outc f
    = outc ... on (liftA2 f) ina
  
  unary
   :: forall f a b c d
    . Applicative f
   => (a -> f b)
   -> (f d -> c)
   -> (b -> d)
   -> a -> c
  unary ina outc f = outc . fmap f . ina
  
  num2num2num = binary toNum fromNum
  num2num2bool = binary toNum fromBool
  bool2bool2bool = binary toBool fromBool
  num2num = unary toNum fromNum
  bool2bool = unary toBool fromBool
  
  toNum
   :: Measure
        (Memo (Expr f (Repr f v)) v)
        (Value (DynCpts e (Repr f v Void)))
   => Repr f v Void -> Either e Double
  toNum m
    = case
      measureRepr m
       :: Value (DynCpts e (Repr f v Void))
      of
      Number n -> Right n
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotNumber)
  fromNum = fmap Number
  
  toBool
   :: Measure
        (Memo (Expr f (Repr f v)) v)
        (Value (DynCpts e (Repr f v Void)))
   => Repr f v Void -> Either e Bool
  toBool m
    = case
      measureRepr m
       :: Value (DynCpts e (Repr f v Void))
      of
      Bool b -> Right b
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotBool)
  fromBool = fmap Bool

valueComponents
 :: (TypeError -> e)
 -> Value (DynCpts e a)
 -> DynCpts e a
valueComponents throwe
  = \case
    Null -> DynCpts Map.empty Nothing
    Comp f -> f
    Number d -> throwDyn (throwe (NoNumberSelf d))
    Text t -> throwDyn (throwe (NoTextSelf t))
    Bool b -> throwDyn (throwe (NoBoolSelf b))

checkExpr
 :: MeasureExpr (DynCpts DynError) v
 => Repr AmbigCpts ()
      (VarName Ident Ident (Import Ident))
 -> ([StaticError], Repr (DynCpts DynError) v Void)
checkExpr m
  = bitransverseRepr
      (fmap (mapError StaticError)
       ... checkComponents
            (DefnError
              . OlappedMatch
              . Text.unpack))
      (checkVar ScopeError)
      m
 <&> (>>= throwRepr . StaticError)

checkVar
 :: (ScopeError -> e)
 -> VarName Ident Ident (Import Ident)
 -> ([e], e)
checkVar throwe n
  = ([e], e)
  where
  e
    = case n of
      Left (Public n)
       -> throwe (NotDefinedPublic (Text.unpack n))
      
      Right (Left (Local n))
       -> throwe (NotDefinedLocal (Text.unpack n))
      
      Right (Right (Import n))
       -> throwe (NotModule (Text.unpack n))

-- Print --

displayExpr
 :: forall f v
  . Measure
      (Memo (Expr f (Repr f v)) v)
      (Value
        (DynCpts DynError
          (Repr f v Void)))
 => Repr f v Void
 -> String
displayExpr m
  = displayValue
      (displayDynCpts displayDynError)
      (measureRepr m
       :: Value (DynCpts DynError (Repr f v Void)))


-- | Dynamic exception

data DynError
  = StaticError StaticError
  | TypeError TypeError
  deriving (Eq, Show)

displayDynError
 :: DynError -> String
displayDynError (StaticError e)
  = displayStaticError e
displayDynError (TypeError e)
  = displayTypeError e
displayDynError _
  = "unknown error"

data StaticError
  = DefnError DefnError
  | ScopeError ScopeError
  | ImportError ImportError
  deriving (Eq, Show)
  
displayStaticError
 :: StaticError -> String
displayStaticError (DefnError e)
  = displayDefnError e
displayStaticError (ScopeError e)
  = displayScopeError e
displayStaticError (ImportError e)
  = displayImportError e

projectDefnError :: StaticError -> Maybe DefnError
projectDefnError (DefnError de) = Just de
projectDefnError _ = Nothing


-- Debug

data Summary f a
  = MoreHidden
  | MoreShown a
  | Summary (Value (Expr f (Summary f) a))
  deriving
    (Show, Functor, Foldable, Traversable)

instance
  (Traversable f, Eq1 f, Eq a) => Eq (Summary f a) 
  where
  Summary va == Summary vb = va == vb
  MoreShown a == MoreShown b = a == b
  _ == _ = False

instance
  (Traversable f, Eq1 f) => Eq1 (Summary f)

instance
  Traversable f => Applicative (Summary f)
  where
  pure = MoreShown
  (<*>) = ap

instance Traversable f => Monad (Summary f) where
  return = pure
  Summary v >>= f
    = Summary ((>>>= f) <$> v)

instance
  (Show1 f, Traversable f) => Show1 (Summary f)
--  where
--  showsPrec1 = showsPrec

summarise
 :: (Functor f, Show1 f, MeasureExpr f r)
 => Integer -> Repr f r a -> Summary f a
summarise n _ | n <= 0 = MoreHidden
summarise n (Var a) = MoreShown a
summarise n (Repr v)
  = Summary
      (v <&> hoistExpr (summarise (n-1)) . unmemo)
