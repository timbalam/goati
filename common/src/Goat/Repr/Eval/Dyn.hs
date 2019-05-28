{-# LANGUAGE ScopedTypeVariables #-}
module Goat.Repr.Eval.Dyn
  ( module Goat.Repr.Eval.Dyn
  , module Goat.Repr.Dyn
  , module Goat.Repr.Preface
  , module Goat.Repr.Expr
  ) where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Dyn
import Goat.Repr.Preface
import Goat.Util ((<&>), (...), fromLeft)
import Data.Align (align)
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
import Data.List (intersperse)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.These (These(..))
import Data.Void (Void)
import Bound (instantiate)


decompose
 :: (TypeError -> e)
 -> Match (Dyn e ()) (Repr (Dyn e) a)
 -> [Repr (Dyn e) a]
decompose throwe (Match (Components (Extend kp p)) m) = vs
  where
    Components (Extend kv ev) = getSelf throwe m
    (kvbind, kvrem) =
      Map.mapEitherWithKey
        (split . throwe . NotComponent)
        (align kp kv)
    vrem = wrapComponents (lift <$> Components (Extend kvrem ev))
    vs = bifoldMap (pure . select) pure (Extend kvbind vrem)
    
    split
     :: e
     -> These (Either e ()) (Either e v)
     -> Either (Either e v) (Either e v)
    split e (This ep) = Left (ep >> Left e)
    split _e (That ev) = Right ev
    split _e (These ep ev) = Left (ep >> ev)
    
    select :: Either e (Repr (Dyn e) a) -> Repr (Dyn e) a
    select = either throwRepr id

getSelf
  :: forall a e . (TypeError -> e)
  -> Repr (Dyn e) a
  -> Dyn e (Repr (Dyn e) a)
getSelf throwe r = d
  where
    d@(Components (Extend kv ev)) =
      subst <$> go mempty (eval throwe r)
  
    go 
      :: Map Text
          (Either e (Scope (Public Ident) (Repr (Dyn e)) a))
      -> Repr (Dyn e) a
      -> Dyn e (Scope (Public Ident) (Repr (Dyn e)) a)
    go kv (Repr (Block (Abs bs))) =
      gogo
        (Map.intersection kv' kv)
        (Map.union kv kv')
        ev
      where 
        Components (Extend kv' ev) =
          substituteBindings 
            (\ p -> map lift (decompose throwe (subst <$> p)))
            bs
    
    go kv a = Components (Extend kv (Right (lift a)))
    
    gogo
     :: Map Text
          (Either e (Scope (Public Ident) (Repr (Dyn e)) a))
     -> Map Text
          (Either e (Scope (Public Ident) (Repr (Dyn e)) a))
     -> Either e (Scope (Public Ident) (Repr (Dyn e)) a)
     -> Dyn e (Scope (Public Ident) (Repr (Dyn e)) a)
    gogo dkv ukv ev =
      if  Map.null dkv 
        then goEither ukv ev
        else case goEither ukv ev of
          Components x
           -> Components
                (x <&>
                  Right . lift . wrapComponents . goEither dkv)
      where
        goEither kv (Left e) = Components (Extend kv (Left e))
        goEither kv (Right v) = go kv (eval throwe (subst v))
    
    subst = instantiate get
    get (Public n) =
      Map.findWithDefault
        (throwRepr
          (fromLeft (throwe (NotComponent n))
            (ev >>= rollupError throwe)))
        n
        (either throwRepr id <$> kv)

throwRepr :: e -> Repr (Dyn e) a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: f (Scope (Public Ident) (Repr f) a) -> Repr f a
wrapComponents c = Repr (Block (Abs (Define c)))

eval
 :: (TypeError -> e)
 -> Repr (Dyn e) a -> Repr (Dyn e) a
eval throwe = go
  where
    go (Var a) = Var a
    go (Repr e) =
      case e of
        Number n -> Repr (Number n)
        Text t   -> Repr (Text t)
        Bool b   -> Repr (Bool b)
        Block f  -> Repr (Block f)
        Null     -> Repr Null
        Sel m n  ->
          case getSelf throwe (go m) of
            Components (Extend kv ev)
             -> either throwRepr go
                  (Map.findWithDefault
                    (ev >>= rollupError throwe >>
                      Left (throwe (NotComponent n)))
                    n
                    kv)
        Add a b  -> num2num2num (+) (go a) (go b)
        Sub a b  -> num2num2num (-) (go a) (go b)
        Mul a b  -> num2num2num (*) (go a) (go b)
        Div a b  -> num2num2num (/) (go a) (go b)
        Pow a b  -> num2num2num (**) (go a) (go b)
        Eq a b   -> num2num2bool (==) (go a) (go b)
        Ne a b   -> num2num2bool (/=) (go a) (go b)
        Lt a b   -> num2num2bool (<) (go a) (go b)
        Le a b   -> num2num2bool (<=) (go a) (go b)
        Gt a b   -> num2num2bool (>) (go a) (go b)
        Ge a b   -> num2num2bool (>=) (go a) (go b)
        Or a b   -> bool2bool2bool (||) (go a) (go b)
        And a b  -> bool2bool2bool (&&) (go a) (go b)
        Not a    -> bool2bool not (go a)
        Neg a    -> num2num negate (go a)

    binary
     :: (a -> Either e b)
     -> (Either e c -> a)
     -> (b -> b -> c)
     -> a -> a -> a
    binary ina outc f a b = outc (f <$> ina a <*> ina b)
    
    unary
     :: (a -> Either e b)
     -> (Either e c -> a)
     -> (b -> c)
     -> a -> a
    unary ina outc f a = outc (f <$> ina a)
    
    num2num2num = binary toNum fromNum
    num2num2bool = binary toNum fromBool
    bool2bool2bool = binary toBool fromBool
    num2num = unary toNum fromNum
    bool2bool = unary toBool fromBool
    
    toNum (Repr (Number n)) = Right n
    toNum m                 =
      rollupError throwe m >> Left (throwe NotNumber)
    fromNum = either throwRepr (Repr . Number)
    
    toBool (Repr (Bool b)) = Right b
    toBool m               =
      rollupError throwe m >> Left (throwe NotBool)
    fromBool = either throwRepr (Repr . Bool)

rollupError
 :: (TypeError -> e)
 -> Repr (Dyn e) a -> Either e ()
rollupError throwe = go
  where
    go v = case getSelf throwe v of
      Components (Extend kv (Left e))
       -> Left e
      Components (Extend kv (Right v))
       | Map.null kv -> Right ()
       | otherwise -> go v


checkExpr
 :: Repr (Multi Identity) (VarName Ident Ident (Import Ident)) 
 -> ([StaticError], Repr (Dyn DynError) Void)
checkExpr m =
  bitransverseRepr
    (checkMulti (DefnError . OlappedMatch))
    (checkVar ScopeError)
    m <&> \ m ->
      transRepr (mapError StaticError) (m >>= wrapComponents)

-- Print --

displayValue :: Repr (Dyn DynError) a -> String
displayValue v =
  case getSelf TypeError v of
    Components (Extend kv ev)
      | Map.null kv -> either displayDynError displayValue' ev
    f               -> displayDyn displayDynError displayValue f
  where
    displayValue' (Repr v) =
      case v of
        Number d -> show d
        Text t   -> Text.unpack t
        Bool b   ->
          "<bool: " ++ if b then "true" else "false" ++ ">"
        Null     -> "<>"
        _        -> "???"

displayErrorList :: (e -> String) -> [e] -> String
displayErrorList displayError es = (foldMap id
  . intersperse "\n") (fmap displayError es)

-- Type error
 
data TypeError =
    NotComponent Ident
  | NotNumber
  | NotText
  | NotBool
  | NoPrimitiveSelf
  deriving (Eq, Show)
  
displayTypeError :: TypeError -> String
displayTypeError (NotComponent i) =
  "error: No component found with name: " ++ showIdent i
displayTypeError NotNumber =
  "error: Number expected"
displayTypeError NotText =
  "error: Text expected"
displayTypeError NotBool =
  "error: Bool expected"
displayTypeError NoPrimitiveSelf =
  "error: Accessed primitive component"

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

