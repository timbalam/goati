{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts #-}
module Goat.Repr.Eval.Dyn
  ( module Goat.Repr.Eval.Dyn
  , Dyn(..), Void
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
newtype Self f = Self (Value (f (Repr (Self f) f Void)))
type MemoRepr f = Repr (Self f) f

instance Measure (Self (Dyn DynError)) (Dyn DynError) where
  measure f =
    Self
      (evalSelf TypeError
        (f >>>= \_ -> throwRepr (TypeError Hole)))

decompose
 :: Measure (Self (Dyn e)) (Dyn e)
 => (TypeError -> e)
 -> Match (Dyn e ()) (MemoRepr (Dyn e) Void)
 -> [MemoRepr (Dyn e) Void]
decompose throwe (Match p v) = vs
  where
    Components (Extend kp ep) = p
    Components (Extend kv ev) =
      valueComponents throwe (evalExpr v)
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
     :: Measure b (Dyn e)
     => Either e (Repr b (Dyn e) a)
     -> Repr b (Dyn e) a
    select = either throwRepr id

throwRepr
 :: Measure b (Dyn e) => e -> Repr b (Dyn e) a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure b f
 => f (Scope (Public Ident) (Repr b f) a) -> Repr b f a
wrapComponents c = repr (Value (Block (Abs (Define c))))

evalExpr 
 :: MemoRepr (Dyn e) Void
 -> Value (Dyn e (MemoRepr (Dyn e) Void))
evalExpr (Repr (Self v) _) = v

getExpr
 :: MemoRepr (Dyn e) Void
 -> Expr (Dyn e) (MemoRepr (Dyn e)) Void
getExpr (Repr _ f) = f

substituteAbs
 :: forall e . Measure (Self (Dyn e)) (Dyn e)
 => (TypeError -> e)
 -> (Scope (Public Ident) (MemoRepr (Dyn e)) Void
     -> MemoRepr (Dyn e) Void)
 -> Abs (Dyn e) (Match (Dyn e ())) (MemoRepr (Dyn e)) Void
 -> Value (Dyn e (MemoRepr (Dyn e) Void))
substituteAbs throwe subst (Abs bs) = go mempty f
  where
    f =
      subst <$>
        substituteBindings
          (\ p -> map lift (decompose throwe (subst <$> p)))
          bs
    
    go
     :: Map Text
          (Either e (MemoRepr (Dyn e) Void))
     -> Dyn e (MemoRepr (Dyn e) Void)
     -> Value (Dyn e (MemoRepr (Dyn e) Void))
    go kv (Components (Extend kv' ev)) =
      gogo
        (Map.intersection kv' kv)
        (Map.union kv kv')
        ev
    
    gogo
     :: Map Text (Either e (MemoRepr (Dyn e) Void))
     -> Map Text (Either e (MemoRepr (Dyn e) Void))
     -> Either e (MemoRepr (Dyn e) Void)
     -> Value (Dyn e (MemoRepr (Dyn e) Void))
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
          where
            extendValue kv v =
              Block
                (Components
                  (Extend kv (Right (repr (Value v)))))

substituteDyn
 :: forall e . Measure (Self (Dyn e)) (Dyn e)
 => (TypeError -> e)
 -> Dyn e (MemoRepr (Dyn e) Void)
 -> Scope (Public Ident) (MemoRepr (Dyn e)) Void
 -> MemoRepr (Dyn e) Void
substituteDyn throwe (Components (Extend kv ev)) =
 instantiate get
  where
    get :: Public Ident -> MemoRepr (Dyn e) Void
    get (Public n) =
      Map.findWithDefault (err n) n (either throwRepr id <$> kv)
    
    err :: Ident -> MemoRepr (Dyn e) Void
    err n =
      throwRepr
        (fromLeft
          (throwe (NotComponent (Text.unpack n)))
          (ev >>= rollupError . evalExpr))

throwValue :: e -> Value (Dyn e a)
throwValue e = Block (throwDyn e)

wrapValue
 :: (Functor f, Measure b f)
 => Value (f (Repr b f a))
 -> Repr b f a
wrapValue v = repr (Value (Abs . Define . fmap lift <$> v))

evalSelf
 :: Measure (Self (Dyn e)) (Dyn e)
 => (TypeError -> e)
 -> Expr (Dyn e) (MemoRepr (Dyn e)) Void
 -> Value (Dyn e (MemoRepr (Dyn e) Void))
evalSelf throwe v = v'
  where
    v' = substituteExpr throwe subst v
    subst = substituteDyn throwe (valueComponents throwe v')

substituteExpr
 :: forall e . Measure (Self (Dyn e)) (Dyn e)
 => (TypeError -> e)
 -> (Scope (Public Ident) (MemoRepr (Dyn e)) Void
     -> MemoRepr (Dyn e) Void)
 -> Expr (Dyn e) (MemoRepr (Dyn e)) Void
 -> Value (Dyn e (MemoRepr (Dyn e) Void))
substituteExpr throwe subst = go
  where
    go = \case
      Value v -> v >>= substituteAbs throwe subst
      Sel m n ->
        let
          Components (Extend kv ev) =
            valueComponents throwe (evalExpr m)
          err =
            ev >>= rollupError . evalExpr >>
              Left (throwe (NotComponent (Text.unpack n)))
        in
          either throwValue evalExpr
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
     :: (a -> Either e b)
     -> (Either e d -> c)
     -> (b -> b -> d)
     -> a -> a -> c
    binary ina outc f a b = outc (f <$> ina a <*> ina b)
    
    unary
     :: (a -> Either e b)
     -> (Either e d -> c)
     -> (b -> d)
     -> a -> c
    unary ina outc f a = outc (f <$> ina a)
    
    num2num2num = binary toNum fromNum
    num2num2bool = binary toNum fromBool
    bool2bool2bool = binary toBool fromBool
    num2num = unary toNum fromNum
    bool2bool = unary toBool fromBool
    
    toNum m =
      case evalExpr m of
        Number n -> Right n
        v        -> rollupError v >> Left (throwe NotNumber)
    fromNum = either throwValue Number
    
    toBool m =
      case evalExpr m of
        Bool b -> Right b
        v      -> rollupError v >> Left (throwe NotBool)
    fromBool = either throwValue Bool

rollupError
 :: Value (Dyn e (MemoRepr (Dyn e) Void)) -> Either e ()
rollupError = go
  where
    go = \case
      Block (Components (Extend _ (Left e)))
       -> Left e
          
      Block (Components (Extend _ (Right v)))
       -> go (evalExpr v)
      
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
 :: Measure b (Dyn DynError)
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

displaySelf
 :: Value (Dyn DynError (MemoRepr (Dyn DynError) Void))
 -> String
displaySelf =
  displayValue
    (displayDyn displayDynError (displaySelf . evalExpr))

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
