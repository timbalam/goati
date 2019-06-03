{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, RankNTypes #-}
module Goat.Repr.Eval.Dyn
  ( module Goat.Repr.Eval.Dyn
  , Dyn(..), Void, Measure(..)
  ) where

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
import Goat.Util ((<&>), (...), fromLeft)
import Control.Monad.Trans (lift)
import Data.Align (align)
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
import Data.Functor (($>))
import Data.List (intersperse)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.These (These(..))
import Data.Void (Void)
import Bound (instantiate, (>>>=))


-- | Unrolled expression
newtype Self f = Self (forall a . Value (f (Repr (Self f) f a)))

self
 :: ( MeasureExpr (Dyn e) c
    , Measure
        (Repr c (Dyn e)) (Value (Dyn e (Repr c (Dyn e) b)))
    )
 => (TypeError -> e)
 -> Expr (Dyn e) (Repr c (Dyn e)) a
 -> Value (Dyn e (Repr c (Dyn e) b))
self throwe f =
  eval throwe (f >>>= \_ -> throwRepr (throwe Hole)) 

type MemoRepr f = Repr (Self f) f

instance MeasureExpr (Dyn DynError) (Self (Dyn DynError)) where
  measureExpr f =
    Self (self TypeError f)

instance
  Measure
    (Repr (Self (Dyn DynError)) (Dyn DynError))
    (Value
      (Dyn DynError
        (Repr (Self (Dyn DynError)) (Dyn DynError) a)))
  where
    measure (Var _) = throwValue (TypeError Hole)
    measure (Repr (Self v) _) = v

instance
  Measure
    (Repr () (Dyn DynError))
    (Value (Dyn DynError (Repr () (Dyn DynError) a)))
  where
    measure (Var _) = throwValue (TypeError Hole)
    measure (Repr () f) = self TypeError f 

decompose
 :: ( MeasureExpr (Dyn e) b
    , Measure (Repr b (Dyn e)) (Value (Dyn e (Repr b (Dyn e) a)))
    )
 => (TypeError -> e)
 -> Match (Dyn e ()) (Repr b (Dyn e) a)
 -> [Repr b (Dyn e) a]
decompose throwe (Match p v) = vs
  where
    Components (Extend kp ep) = p
    Components (Extend kv ev) =
      valueComponents throwe (measure v)
    (kvbind, kvrem) =
      Map.mapEitherWithKey
        (split . throwe . NotComponent . Text.unpack)
        (align kp kv)
    vrem =
      ep $>
        wrapComponents (lift <$> Components (Extend kvrem ev))
    vs =
      bifoldMap
        (pure . select)
        (pure . select)
        (Extend kvbind vrem)
    
    split
     :: e
     -> These (Either e ()) (Either e v)
     -> Either (Either e v) (Either e v)
    split e (This ep) = Left (ep >> Left e)
    split _e (That ev) = Right ev
    split _e (These ep ev) = Left (ep >> ev)
    
    select
     :: Measure (Expr (Dyn e) (Repr b (Dyn e))) b
     => Either e (Repr b (Dyn e) a)
     -> Repr b (Dyn e) a
    select = either throwRepr id

throwRepr
 :: Measure (Expr (Dyn e) (Repr b (Dyn e))) b
 => e -> Repr b (Dyn e) a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure (Expr f (Repr b f)) b
 => f (Scope (Public Ident) (Repr b f) a) -> Repr b f a
wrapComponents c = repr (Value (Block (Abs (Define c))))

getExpr :: Repr b f a -> Expr f (Repr b f) a
getExpr (Repr _ f) = f

substituteAbs
 :: forall b e a . 
    ( MeasureExpr (Dyn e) b
    , Measure (Repr b (Dyn e)) (Value (Dyn e (Repr b (Dyn e) a)))
    )
 => (TypeError -> e)
 -> (Scope (Public Ident) (Repr b (Dyn e)) a
     -> Repr b (Dyn e) a)
 -> Abs (Dyn e) (Match (Dyn e ())) (Repr b (Dyn e)) a
 -> Value (Dyn e (Repr b (Dyn e) a))
substituteAbs throwe subst (Abs bs) = go mempty f
  where
    f =
      subst <$>
        substituteBindings
          (\ p -> map lift (decompose throwe (subst <$> p)))
          bs
    
    go
     :: Measure (Expr (Dyn e) (Repr b (Dyn e))) b
     => Map Text (Either e (Repr b (Dyn e) a))
     -> Dyn e (Repr b (Dyn e) a)
     -> Value (Dyn e (Repr b (Dyn e) a))
    go kv (Components (Extend kv' ev)) =
      gogo
        (Map.intersection kv' kv)
        (Map.union kv kv')
        ev
    
    gogo
     :: Measure (Expr (Dyn e) (Repr b (Dyn e))) b
     => Map Text (Either e (Repr b (Dyn e) a))
     -> Map Text (Either e (Repr b (Dyn e) a))
     -> Either e (Repr b (Dyn e) a)
     -> Value (Dyn e (Repr b (Dyn e) a))
    gogo dkv ukv ev =
      if  Map.null dkv 
        then goEither ukv ev
        else goEither ukv ev <&> \ (Components x) ->
          Components (x <&> Right . wrapValue . goEither dkv)
      where
        goEither kv (Left e) =
          Block (Components (Extend kv (Left e)))
        goEither kv (Right v) =
          case substituteExpr throwe subst (getExpr v) of
            Block f -> go kv f
            Number d -> extendValue kv (Number d)
            Text t -> extendValue kv (Text t)
            Bool b -> extendValue kv (Bool b)
            Null -> extendValue kv Null
    
    extendValue
     :: Measure (Expr (Dyn e) (Repr b (Dyn e))) b
     => Map Text (Either e (Repr b (Dyn e) a))
     -> Value (Abs (Dyn e) (Match (Dyn e ())) (Repr b (Dyn e)) a)
     -> Value (Dyn e (Repr b (Dyn e) a))
    extendValue kv v =
      Block
        (Components
          (Extend kv (Right (repr (Value v)))))

substituteDyn
 :: forall b e a .
    ( MeasureExpr (Dyn e) b
    , Measure
        (Repr b (Dyn e)) (Value (Dyn e (Repr b (Dyn e) a)))
    )
 => (TypeError -> e)
 -> Dyn e (Repr b (Dyn e) a)
 -> Scope (Public Ident) (Repr b (Dyn e)) a
 -> Repr b (Dyn e) a
substituteDyn throwe (Components (Extend kv ev)) =
 instantiate get
  where
    get :: Public Ident -> Repr b (Dyn e) a
    get (Public n) =
      Map.findWithDefault
        (err n)
        n
        (either throwRepr id <$> kv)
    
    err
     :: Ident -> Repr b (Dyn e) a
    err n =
      throwRepr
        (fromLeft
          (throwe (NotComponent (Text.unpack n)))
          (ev >>= rollupError . measure'))
    
    measure'
     :: Repr b (Dyn e) a -> Value (Dyn e (Repr b (Dyn e) a))
    measure' = measure

throwValue :: e -> Value (Dyn e a)
throwValue e = Block (throwDyn e)

wrapValue
 :: (Functor f, MeasureExpr f b)
 => Value (f (Repr b f a))
 -> Repr b f a
wrapValue v = repr (Value (Abs . Define . fmap lift <$> v))

eval
 :: ( MeasureExpr (Dyn e) b
    , Measure
        (Repr b (Dyn e)) (Value (Dyn e (Repr b (Dyn e) a)))
    )
 => (TypeError -> e)
 -> Expr (Dyn e) (Repr b (Dyn e)) a
 -> Value (Dyn e (Repr b (Dyn e) a))
eval throwe v = v'
  where
    v' = substituteExpr throwe subst v
    subst = substituteDyn throwe (valueComponents throwe v')

substituteExpr
 :: forall b e a .
    ( MeasureExpr (Dyn e) b
    , Measure
        (Repr b (Dyn e)) (Value (Dyn e (Repr b (Dyn e) a)))
    )
 => (TypeError -> e)
 -> (Scope (Public Ident) (Repr b (Dyn e)) a
      -> Repr b (Dyn e) a)
 -> Expr (Dyn e) (Repr b (Dyn e)) a
 -> Value (Dyn e (Repr b (Dyn e) a))
substituteExpr throwe subst = go
  where
    go = \case
      Value v -> v >>= substituteAbs throwe subst
      Sel m n ->
        let
          Components (Extend kv ev) =
            valueComponents throwe (measure m)
          err =
            ev >>= rolle . measure >>
              Left (throwe (NotComponent (Text.unpack n)))
          
          measureRepr
           :: Repr b (Dyn e) a -> Value (Dyn e (Repr b (Dyn e) a))
          measureRepr = measure
        in
          either throwValue measureRepr
            (Map.findWithDefault err n kv)
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
     :: forall e a b c d . (a -> Either e b)
     -> (Either e d -> c)
     -> (b -> b -> d)
     -> a -> a -> c
    binary ina outc f a b = outc (f <$> ina a <*> ina b)
    
    unary
     :: forall e a b c d . (a -> Either e b)
     -> (Either e d -> c)
     -> (b -> d)
     -> a -> c
    unary ina outc f a = outc (f <$> ina a)
    
    num2num2num = binary toNum fromNum
    num2num2bool = binary toNum fromBool
    bool2bool2bool = binary toBool fromBool
    num2num = unary toNum fromNum
    bool2bool = unary toBool fromBool
    
    toNum :: Repr b (Dyn e) a -> Either e Double
    toNum m =
      case measure m of
        Number n -> Right n
        v        -> rolle v >> Left (throwe NotNumber)
    fromNum = either throwValue Number
    
    toBool :: Repr b (Dyn e) a -> Either e Bool
    toBool m =
      case measure m of
        Bool b -> Right b
        v      -> rolle v >> Left (throwe NotBool)
    fromBool = either throwValue Bool
    
    rolle :: Value (Dyn e (Repr b (Dyn e) a)) -> Either e ()
    rolle = rollupError

rollupError
 :: Measure m (Value (Dyn e (m a)))
 => Value (Dyn e (m a)) -> Either e ()
rollupError = go
  where
    go = \case
      Block (Components (Extend _ (Left e)))
       -> Left e
          
      Block (Components (Extend _ (Right v)))
       -> go (measure v)
      
      _
       -> Right  ()

valueComponents
 :: (TypeError -> e) -> Value (Dyn e a) -> Dyn e a
valueComponents throwe = \case
  Block f  -> f
  Number d -> throwDyn (throwe (NoNumberSelf d))
  Text t   -> throwDyn (throwe (NoTextSelf t))
  Bool b   -> throwDyn (throwe (NoBoolSelf b))

checkExpr
 :: MeasureExpr (Dyn DynError) b
 => Repr () (Multi Identity) (VarName Ident Ident (Import Ident))
 -> ([StaticError], Repr b (Dyn DynError) Void)
checkExpr m =
  bitransverseRepr
    (fmap (mapError StaticError) ...
      checkMulti (DefnError . OlappedMatch . Text.unpack))
    (checkVar ScopeError)
    m <&> \ m -> m >>= throwRepr . StaticError

checkVar
 :: (ScopeError -> e)
 -> VarName Ident Ident (Import Ident)
 -> ([e], e)
checkVar throwe n = ([e], e)
  where
    e =
      case n of
        Left (Public n)
         -> throwe (NotDefinedPublic (Text.unpack n))
        
        Right (Left (Local n))
         -> throwe (NotDefinedLocal (Text.unpack n))
        
        Right (Right (Import n))
         -> throwe (NotModule (Text.unpack n))

-- Print --

displayExpr
 :: forall m a . Measure m (Value (Dyn DynError (m a)))
 => m a
 -> String
displayExpr =
  displayValue
    (displayDyn displayDynError displayExpr)
    . measure'
  where
    measure' :: m a -> Value (Dyn DynError (m a))
    measure' = measure


-- | Dynamic exception

data DynError =
    StaticError StaticError
  | TypeError TypeError
  deriving (Eq, Show)

displayDynError :: DynError -> String
displayDynError (StaticError e) = displayStaticError e
displayDynError (TypeError e)   = displayTypeError e
displayDynError _               = "unknown error"

data StaticError =
    DefnError DefnError
  | ScopeError ScopeError
  | ImportError ImportError
  deriving (Eq, Show)
  
displayStaticError :: StaticError -> String
displayStaticError (DefnError e)  = displayDefnError e
displayStaticError (ScopeError e) = displayScopeError e
displayStaticError (ImportError e) = displayImportError e

projectDefnError :: StaticError -> Maybe DefnError
projectDefnError (DefnError de) = Just de
projectDefnError _ = Nothing
