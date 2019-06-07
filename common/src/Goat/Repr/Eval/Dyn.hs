{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, RankNTypes #-}
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
import Goat.Util
  ( (<&>), (...), restrictKeys ) --fromLeft
import Control.Monad.Trans (lift)
import Data.Align (align)
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
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

import Debug.Trace


-- | Unrolled expression
data Eval f
  = Eval
      (f (Repr f (Eval f) Void))

bindHoles
 :: (TypeError -> e)
 -> Expr (DynCpts e) (Repr (DynCpts e) v) a
 -> Expr (DynCpts e) (Repr (DynCpts e) v) Void
bindHoles throwe f
  = f >>>= \_ -> throwRepr (throwe Hole)

type MemoRepr f = Repr f (Eval f)

instance
  MeasureExpr
    (DynCpts DynError) (Eval (DynCpts DynError)) 
  where
  measureExpr f
    = Eval (eval TypeError (bindHoles TypeError f))

instance
  Measure
    (Memo f (Eval (DynCpts DynError)))
    (DynCpts DynError
      (Repr (DynCpts DynError)
        (Eval (DynCpts DynError))
        Void))
  where
  measure (Memo v _) = v

instance
  Measure
    (Memo 
      (Expr (DynCpts (DynError))
        (Repr (DynCpts DynError) ()))
      ())
    (DynCpts DynError
      (Repr (DynCpts DynError) () Void))
  where
  measure f
    = eval TypeError (bindHoles TypeError f) 

decompose
 :: ( MeasureExpr (DynCpts e) b
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (DynCpts e (Repr (DynCpts e) v Void))
    )
 => (TypeError -> e)
 -> DynCpts e ()
 -> Repr (DynCpts e) b Void
 -> [Repr (DynCpts e) b Void]
decompose throwe (DynCpts kp mep) ~(Repr v)
  = trace "decompose" ms
  where
  DynCpts km mem
    = valueComponents throwe (v >>= measure)
  
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
    = Repr
        (v >>= getRemaining (Map.keysSet kp))
  
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
   :: Measure
        (Expr (DynCpts e) (Repr (DynCpts e) b)) b
   => Either e (Repr (DynCpts e) b a)
   -> Repr (DynCpts e) b a
  select = either throwRepr id

throwRepr
 :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
 => e -> Repr b (DynCpts e) a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure (Expr f (Repr b f)) b
 => f (Scope (Super Ident)
        (Scope (Public Ident) (Repr b f)) a)
 -> Repr b f a
wrapComponents c
  = Repr (Comp (memo (Ext (Define c) emptyRepr)))

getRemaining
 :: Measure (Expr (DynCpts e) (Repr (DynCpts e) v)) v
 => (TypeError -> e)
 -> Set Text
 -> Memo (Expr (DynCpts e) (Repr (DynCpts e) v)) v a
 -> Value
      (Memo
        (Expr (DynCpts e) (Repr (DynCpts e) v)) v a)
getRemaining throwe ks (Memo _ f)
  = simplify
      throwe
      (\ bs v
       -> deleteComponents bs <$> v)
      f
 <&> (`id` ks)

deleteComponents
 :: (Measure
      (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
 => Bindings (DynCpts e) (DynCpts e)
      (Scope (Super Ident)
        (Scope (Public Ident)
          (Repr (DynCpts e) v)))
      a
 -> (Set Text
     -> Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v))
          v a)
 -> Set Text
 -> Memo (Expr (DynCpts e) (Repr (DynCpts e) v)) v a
deleteComponents bs f ks
  = memo (Ext bs' (Repr (Comp (f ks'))))
  where
    (ks', bs')
      = transverseBindings
          (\ (DynCpts km me)
           -> ( maybe
                  (Set.difference
                    ks (Map.keysSet km))
                  (\_ -> Set.empty)
                  me
              , DynCpts (restrictKeys km ks) me
              ))
          bs

getDyn
 :: forall e v a
  . MeasureExpr (DynCpts e) v
 => (TypeError -> e)
 -> DynCpts e (Repr (DynCpts e) v a)
 -> Ident -> Repr (DynCpts e) v a
getDyn throwe ~(DynCpts km me)
  = trace "getDyn" get
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

throwValue :: e -> Value (DynCpts e a)
throwValue e = Block (throwDyn e)

wrapValue
 :: (Functor f, MeasureExpr f v)
 => Value (f (Repr f v a))
 -> Repr f v a
wrapValue v
  = Repr
      (Comp
        (memo
          (Ext
            (Define . fmap lift <$> v)
            emptyRepr)))

eval
 :: ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v) v))
        (DynCpts e (Repr (DynCpts e) v Void))
    )
 => (TypeError -> e)
 -> Expr (DynCpts e) (Repr (DynCpts e) v) Void
 -> Value (DynCpts e (Repr (DynCpts e) v Void))
eval throwe f
  = trace "eval" v'
  where
  v'
    = simplify
        throwe
        (\ bs v
         -> v
         <$> substituteExt throwe subst bs)
        f
   <&> fmap memoSimplify

  subst
    = instantiate 
        (\ (Public n)
         -> getDyn
              throwe (valueComponents throwe v') n)

substituteExt
 :: MeasureExpr (DynCpts e) v
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
    = instantiate (\ (Super n) -> lift (getDyn c n))

extendComponents
 :: DynCpts e (Repr (DynCpts e) v) Void
 -> DynCpts e (Repr (DynCpts e) v) Void
 -> DynCpts e (Repr (DynCpts e) v) Void
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
    , Measure f v
    )
 => TypeError -> e
 -> Repr (DynCpts e) v Void 
 -> Repr (DynCpts e) v Void
memoSimplify throwe (Repr v)
  = Repr
      (v
       >>= \ (Memo _ f)
           -> simplify throwe
                (\ bs v
                 -> Comp (memo (Ext bs (Repr v))))
                f)

simplify
 :: forall e v a
  . ( MeasureExpr (DynCpts e) v
    , Measure
        (Memo
          (Expr (DynCpts e) (Repr (DynCpts e) v)) v)
        (Value (DynCpts e (Repr (DynCpts e) v Void)))
    )
 => (TypeError -> e)
 -> (Bindings
      (DynCpts e) (DynCpts e)
      (Scope (Super Ident)
        (Scope (Public Ident) (Repr (DynCpts e) v)))
      Void
     -> Value a
     -> Value a)
 -> Expr (DynCpts e) (Repr (DynCpts e) v) Void
 -> Value a
simplify throwe simplifyExt f
  = goExpr (tagExpr "simplify" f)
  where
  goMemo (Memo _ f) = goExpr f
  
  goExpr
    = \case
      Ext bs (Repr v) 
       -> simplifyExt bs (v >>= goMemo)

      Sel (Repr v) n
       -> let
          DynCpts km me
            = valueComponents throwe (v >>= measure)
          err
            = fromMaybe
                (throwe
                  (NotComponent (Text.unpack n)))
                me
          in
          case
          Map.findWithDefault (Left err) n km
          of
          Left e -> throwValue e
          Right (Repr v) -> v >>= goMemo
      
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
   :: forall e a b c d
    . (a -> Either e b)
   -> (Either e d -> c)
   -> (b -> b -> d)
   -> a -> a -> c
  binary ina outc f a b
    = outc (f <$> ina a <*> ina b)
  
  unary
   :: forall e a b c d
    . (a -> Either e b)
   -> (Either e d -> c)
   -> (b -> d)
   -> a -> c
  unary ina outc f a = outc (f <$> ina a)
  
  num2num2num = binary toNum fromNum
  num2num2bool = binary toNum fromBool
  bool2bool2bool = binary toBool fromBool
  num2num = unary toNum fromNum
  bool2bool = unary toBool fromBool
  
  toNum
   :: Repr (DynCpts e) v Void -> Either e Double
  toNum (Repr v)
    = case v >>= measure of
      Number n -> Right n
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotNumber)
  fromNum = either throwValue Number
  
  toBool
   :: Repr (DynCpts e) v Void -> Either e Bool
  toBool (Repr v)
    = case v >>= measure of
      Bool b -> Right b
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotBool)
  fromBool = either throwValue Bool

valueComponents
 :: MeasureExpr (DynCpts e) v
 => (TypeError -> e)
 -> Value (DynCpts e (Repr (DynCpts e) v a))
 -> DynCpts e (Repr (DynCpts e) v a)
valueComponents throwe
  = \case
    Null -> DynCpts Map.empty Nothing
    Block f -> f
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
 :: forall m a
  . Measure m (Value (DynCpts DynError (m a)))
 => m a
 -> String
displayExpr
  = displayValue
      (displayDynCpts displayDynError displayExpr)
  . measure'
  where
  measure' :: m a -> Value (DynCpts DynError (m a))
  measure' = measure


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

tagEither
 :: String -> Either a b -> Either a b
tagEither tag e
  = trace (tag ++ lab e) e
  where
  lab
    = \case
      Left{} -> "/Left"
      Right{} -> "/Right"

tagComponents
 :: String -> DynCpts e a -> DynCpts e a
tagComponents tag (DynCpts kem me)
  = trace (tag ++ "/" ++ show (Map.keys kem))
    (DynCpts kem me)

tagValue
 :: String -> Value a -> Value a
tagValue tag v
  = trace (tag ++ lab v) v
  where
  lab
    = \case 
      Comp{} -> "/Comp"
      Number{} -> "/Number"
      Text{} -> "/Text"
      Null -> "/Null"
      Bool{} -> "/Bool"

tagExpr
 :: String -> Expr f m a -> Expr f m a
tagExpr tag f
  = trace (tag ++ lab f) f
  where
  lab
    = \case
      Ext{} -> "/Ext"
      Sel _ n -> "/Sel/" ++ Text.unpack n
      Add{} -> "/Add"
      Sub{} -> "/Sub"
      Mul{} -> "/Mul"
      Div{} -> "/Div"
      Pow{} -> "/Pow"
      Eq{}  -> "/Eq"
      Ne{}  -> "/Ne"
      Lt{}  -> "/Lt"
      Le{}  -> "/Le"
      Gt{}  -> "/Gt"
      Ge{}  -> "/Ge"
      Or{}  -> "/Or"
      And{} -> "/And"
      Not{} -> "/Not"
      Neg{} -> "/Neg"

