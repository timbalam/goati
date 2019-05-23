{-# LANGUAGE ScopedTypeVariables #-}
module Goat.Repr.Eval.Dyn where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.Dyn
import Goat.Util ((<&>), (...))
import Data.Bifunctor (first)
import Data.Bifoldable (bifoldMap)
import qualified Data.Map as Map
import Data.Align (align)
import Data.These (These(..))
import Bound (instantiate)


decompose
 :: Match (Dyn TypeError ()) (Repr (Dyn TypeError) a)
 -> [Repr (Dyn TypeError) a]
decompose (Match (Components (Extend kp p)) m) = vs
  where
    Components (Extend kv ev) = getSelf m
    (kvbind, kvrem) =
      Map.mapEitherWithKey
        (split . NotComponent)
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
    select = either throwDyn id

getSelf
  :: forall a . Repr (Dyn TypeError) a
  -> Dyn TypeError (Repr (Dyn TypeError) a)
getSelf r = d
  where
    d@(Components (Extend kv _)) = subst <$> go mempty r
  
    go 
      :: Map Text
          (Either TypeError 
            (Scope (Public Ident) (Repr (Dyn TypeError)) a))
      -> Repr (Dyn TypeError) a
      -> Dyn TypeError
          (Scope (Public Ident) (Repr (Dyn TypeError)) a)
    go kv (Repr (Block (Abs bs))) =
      gogo
        (Map.intersection kv' kv)
        (Map.union kv kv')
        ev
      where 
        Components (Extend kv' ev) =
          substituteBindings 
            (\ p -> map lift (decompose (subst <$> p)))
            bs
      
    go kv a = Components (Extend kv (Right (lift a)))
    
    gogo
     :: Map Text
          (Either TypeError
            (Scope (Public Ident) (Repr (Dyn TypeError)) a))
     -> Map Text
          (Either TypeError
            (Scope (Public Ident) (Repr (Dyn TypeError)) a))
     -> Either 
          TypeError
          (Scope (Public Ident) (Repr (Dyn TypeError)) a)
     -> Dyn TypeError
          (Scope (Public Ident) (Repr (Dyn TypeError)) a)
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
        goEither kv (Right v) = go kv (subst v)
    
    subst = instantiate get
    get (Public n) =
      Map.findWithDefault
        (throwDyn (NotComponent n))
        n
        (either throwDyn id <$> kv)

    
throwDyn :: e -> Repr (Dyn e) a
throwDyn e =
  wrapComponents (Components (Extend mempty (Left e)))

wrapComponents
 :: f (Scope (Public Ident) (Repr f) a) -> Repr f a
wrapComponents c = Repr (Block (Abs (Define c)))


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
  "error: No component found with name: " ++ show i
displayTypeError NotNumber =
  "error: Number expected"
displayTypeError NotText =
  "error: Text expected"
displayTypeError NotBool =
  "error: Bool expected"
displayTypeError NoPrimitiveSelf =
  "error: Accessed primitive component"