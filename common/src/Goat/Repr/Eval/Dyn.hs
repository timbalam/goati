{-# LANGUAGE ScopedTypeVariables #-}
module Goat.Repr.Eval.Dyn where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Dyn
import Goat.Util ((<&>), (...), fromLeft)
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
import qualified Data.Map as Map
import Data.Align (align)
import Data.These (These(..))
import Bound (instantiate)


decompose
 :: (TypeError -> e)
 -> Match (Dyn e ()) (Repr (Dyn e) a)
 -> [Repr (Dyn e) a]
decompose throw (Match (Components (Extend kp p)) m) = vs
  where
    Components (Extend kv ev) = getSelf throw m
    (kvbind, kvrem) =
      Map.mapEitherWithKey
        (split . throw . NotComponent)
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
getSelf throw r = d
  where
    d@(Components (Extend kv ev)) =
      subst <$> go mempty (eval throw r)
  
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
            (\ p -> map lift (decompose throw (subst <$> p)))
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
        goEither kv (Right v) = go kv (eval throw (subst v))
    
    subst = instantiate get
    get (Public n) =
      Map.findWithDefault
        (throwRepr
          (fromLeft (throw (NotComponent n))
            (ev >>= rollupError throw)))
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
eval throw = go
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
          case getSelf throw (go m) of
            Components (Extend kv ev)
             -> either throwRepr go
                  (Map.findWithDefault
                    (ev >>= rollupError throw >>
                      Left (throw (NotComponent n)))
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
      rollupError throw m >> Left (throw NotNumber)
    fromNum = either throwRepr (Repr . Number)
    
    toBool (Repr (Bool b)) = Right b
    toBool m               =
      rollupError throw m >> Left (throw NotBool)
    fromBool = either throwRepr (Repr . Bool)

rollupError
 :: (TypeError -> e)
 -> Repr (Dyn e) a -> Either e ()
rollupError throw = go
  where
    go v = case getSelf throw v of
      Components (Extend kv (Left e))
       -> Left e
      Components (Extend kv (Right v))
       | Map.null kv -> Right ()
       | otherwise -> go v


checkExpr
 :: Repr (Multi Identity) (VarName Void Ident (Import Ident)) 
 -> ([StaticError], Repr (Dyn DynError) Void)
checkExpr m =
  bitransverseRepr
    (checkMulti (StaticError . DefnError . OlappedMatch))
    (checkVar (StaticError . ScopeError))
    m <&> \ m -> m >>= wrapComponents
    


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

