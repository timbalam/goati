{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, RankNTypes #-}
module Goat.Repr.Eval.DynCpts
  ( module Goat.Repr.Eval.DynCpts
  , DynCpts(..), Void, Measure(..)
  )
where

import Goat.Repr.Pattern
import Goat.Repr.Expr
import Goat.Repr.DynCpts
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
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.Semigroup ((<>))
import qualified Data.Text as Text
import Data.These (These(..))
import Data.Void (Void)
import Bound (instantiate, (>>>=))

import Debug.Trace


-- | Unrolled expression
newtype Eval f
  = Eval (f (Repr f (Eval f) Void))

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
    (Memo f (Eval (DynCpts DynError)) a)
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
      ()
      a)
    (DynCpts DynError
      (Repr (DynCpts DynError) () Void))
  where
  measure = eval TypeError (bindHoles TypeError f) 

decompose
 :: ( MeasureExpr (DynCpts e) b
    , Measure
        (Repr b (DynCpts e))
        (Value (DynCpts e (Repr b (DynCpts e) a)))
    )
 => (TypeError -> e)
 -> DynCpts e ()
 -> Repr b (DynCpts e) a
 -> [Repr b (DynCpts e) a]
decompose throwe (Components (Extend kp ep)) v
  = trace "decompose" vs
  where
  Components (Extend kv ev)
    = valueComponents throwe (measure v)
  
  (kvbind, kvrem)
    = Map.mapEitherWithKey
        (split . throwe . NotComponent . Text.unpack)
        (align kp kv)
  
  vrem
    = ep
   $> wrapComponents
        (lift <$> Components (Extend kvrem ev))
  
  vs
    = bifoldMap
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
   :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
   => Either e (Repr b (DynCpts e) a)
   -> Repr b (DynCpts e) a
  select = either throwRepr id

throwRepr
 :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
 => e -> Repr b (DynCpts e) a
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure (Expr f (Repr b f)) b
 => f (Scope (Public Ident) (Repr b f) a)
 -> Repr b f a
wrapComponents c
  = repr (Value (Block (Abs (Define c))))

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
tagComponents tag (Components (Extend kem em))
  = trace (tag ++ "/" ++ show (Map.keys kem))
    (Components (Extend kem (tagEither tag em)))

substituteAbs
 :: forall b e . 
    ( MeasureExpr (DynCpts e) b
    , Measure
        (Repr b (DynCpts e))
        (Value (DynCpts e (Repr b (DynCpts e) Void)))
    )
 => (TypeError -> e)
 -> (Scope (Public Ident) (Repr b (DynCpts e)) Void
     -> Repr b (DynCpts e) Void)
 -> Abs (DynCpts e) (DynCpts e) (Repr b (DynCpts e)) Void
 -> DynCpts e (Repr b (DynCpts e) Void)
substituteAbs throwe subst (Abs bs)
  = tagComponents "substituteAbs/Out"
    (fillComponents
      (tagComponents "substituteAbs/In" f))
  where
  f
    = subst 
   <$> substituteBindings
        (\ p v
         -> map
              lift
              (decompose throwe p (subst v)))
        bs
  
  fillComponents
   :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
   => DynCpts e (Repr b (DynCpts e) Void)
   -> DynCpts e (Repr b (DynCpts e) Void)
  fillComponents
    (Components (Extend kem (Right (Repr _ f))))
    = go kem f
    where
    go
     :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
     => Map Text (Either e (Repr b (DynCpts e) Void))
     -> Expr (DynCpts e) (Repr b (DynCpts e)) Void
     -> DynCpts e (Repr b (DynCpts e) Void)
    go kem f
      = case
        tagValue "fillComponents"
        (tagComponents "fillComponents"
         <$> substituteExpr throwe subst f)
        of
        Block (Components (Extend nkem em))
         -> let
            ukem = Map.union kem nkem
            dkem = Map.intersection nkem kem
            in
            case em of
            Right (Repr _ f)
             -> case go ukem f of
                Components (Extend ukem' em')
                 -> extendValue ukem'
                      (Block
                        (Components
                          (Extend dkem em')))
            _
             -> extendValue ukem
                  (Block
                    (Components (Extend dkem em)))
        Number d -> extendValue kem (Number d)
        Text t   -> extendValue kem (Text t)
        Bool b   -> extendValue kem (Bool b)
        Null     -> extendValue kem Null
  fillComponents c = c
      
  extendValue
   :: forall e b f a
    . MeasureExpr f b
   => Functor f
   => Map Text (Either e (Repr b f a))
   -> Value (f (Repr b f a))
   -> DynCpts e (Repr b f a)
  extendValue kem v =
    Components
      (Extend kem (Right (wrapValue v)))
{-
versions
 :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
 => DynCpts e (Repr b (DynCpts e) Void)
 -> DynCpts e (Repr b (DynCpts e) Void)
versions (Components (Extend kem em))
  = uncurry componentsFromVersions
      (componentVersions kem em)
  where
  componentVersions 
   :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
   => DynCpts e (Repr b (DynCpts e) Void)
   -> ( Map Text
          (NonEmpty (Either e (Repr b (DynCpts e) Void)))
      , Either e (Value a)
      )
  sortComponents (Components (Extend kv e))
    = case
      traceEither
        ("sortComponents/"
         ++ show (Map.keys kv))
        e
      of
      Right v
       -> 
        first
          (Map.unionWith (<>) (pure <$> kv))
          (sortExpr (getExpr v))
      
      Left e
       -> (pure <$> kv, Left e)
  
  sortExpr
   :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
   => Expr (DynCpts e) (Repr b (DynCpts e)) Void
   -> ( Map Text
          (NonEmpty (Either e (Repr b (DynCpts e) Void)))
      , Either e (Value a)
      )
  sortExpr f
    = case
      substituteExpr throwe subst f
      of
      Block c  -> sortComponents c
      Number d -> justValue (Number d)
      Text t   -> justValue (Text t)
      Bool b   -> justValue (Bool b)
      Null     -> justValue Null
    where
    justValue v = (Map.empty, Right v)
  
  components
   :: Measure (Expr (DynCpts e) (Repr b (DynCpts e))) b
   => Map Text
        (NonEmpty (Either e (Repr b (DynCpts e) Void)))
   -> Either e (Value (DynCpts e (Repr b (DynCpts e) Void)))
   -> DynCpts e (Repr b (DynCpts e) Void)
  components kems ev
    = Components (Extend kem em)
    where
    em
      = if Map.null kems' then
        wrapValue <$> ev else
        Right
          (wrapValue (Block (components kems' ev)))
    (kem, kems') = splitUncons kems
    splitUncons
     :: Map k (NonEmpty v)
     -> (Map k v, Map k (NonEmpty v))
    splitUncons kv
      = ( NonEmpty.head <$> kv
        , Map.mapMaybe
            (NonEmpty.nonEmpty . NonEmpty.tail) kv
        )
-}
substituteDyn
 :: forall b e a .
    ( MeasureExpr (DynCpts e) b
    , Measure
        (Repr b (DynCpts e))
        (Value (DynCpts e (Repr b (DynCpts e) a)))
    )
 => (TypeError -> e)
 -> DynCpts e (Repr b (DynCpts e) a)
 -> Scope (Public Ident) (Repr b (DynCpts e)) a
 -> Repr b (DynCpts e) a
substituteDyn throwe ~(Components (Extend kv ev))
  = trace "substituteDyn" (instantiate get)
  where
  get :: Public Ident -> Repr b (DynCpts e) a
  get (Public n)
    = Map.findWithDefault
        (err n)
        n
        (either throwRepr id <$> kv)
    
  err
   :: Ident -> Repr b (DynCpts e) a
  err n
    = throwRepr
        (fromLeft
          (throwe (NotComponent (Text.unpack n)))
          (ev >>= rollupError . measure'))
    
  measure'
   :: Repr b (DynCpts e) a
   -> Value (DynCpts e (Repr b (DynCpts e) a))
  measure' = measure

throwValue :: e -> Value (DynCpts e a)
throwValue e = Block (throwDyn e)

wrapValue
 :: (Functor f, MeasureExpr f b)
 => Value (f (Repr b f a))
 -> Repr b f a
wrapValue v
  = repr (Value (Abs . Define . fmap lift <$> v))

eval
 :: ( MeasureExpr (DynCpts e) b
    , Measure
        (Repr b (DynCpts e))
        (Value (DynCpts e (Repr b (DynCpts e) Void)))
    )
 => (TypeError -> e)
 -> Expr (DynCpts e) (Repr b (DynCpts e)) Void
 -> Value (DynCpts e (Repr b (DynCpts e) Void))
eval throwe f
  = trace "eval" v'
  where
  v'
    = substituteExpr throwe subst f

  subst
    = substituteDyn
       throwe
       (valueComponents throwe v')

tagValue
 :: String -> Value a -> Value a
tagValue tag v
  = trace (tag ++ lab v) v
  where
  lab
    = \case 
      Block{} -> "/Block"
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
      Value{} -> "/Value"
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

substituteExpr
 :: forall b e
  . ( MeasureExpr (DynCpts e) b
    , Measure
        (Repr b (DynCpts e))
        (Value (DynCpts e (Repr b (DynCpts e) Void)))
    )
 => (TypeError -> e)
 -> (Scope (Public Ident) (Repr b (DynCpts e)) Void
      -> Repr b (DynCpts e) Void)
 -> Expr (DynCpts e) (Repr b (DynCpts e)) Void
 -> Value (DynCpts e (Repr b (DynCpts e) Void))
substituteExpr throwe subst f
  = go (tagExpr "substituteExpr" f)
  where
  go
    = \case
      Value v
       -> tagValue "substituteExpr"
          (v <&> substituteAbs throwe subst)

      Sel m n
       -> let
          Components (Extend kv ev)
            = valueComponents
                throwe
                (measure m)
          err
            = ev
           >>= rolle . measure
           >> Left
                (throwe
                  (NotComponent
                    (Text.unpack n)))
          in
          case Map.findWithDefault err n kv of
          Left e -> throwValue e
          Right (Repr _ f) -> go f
      
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
  
  toNum :: Repr b (DynCpts e) Void -> Either e Double
  toNum m
    = case measure m of
      Number n
       -> Right n
      
      v
       -> rolle v
       >> Left (throwe NotNumber)
  fromNum = either throwValue Number
  
  toBool :: Repr b (DynCpts e) Void -> Either e Bool
  toBool m
    = case measure m of
      Bool b
       -> Right b
      
      v
       -> rolle v
       >> Left (throwe NotBool)
  fromBool = either throwValue Bool
  
  rolle 
   :: Value (DynCpts e (Repr b (DynCpts e) Void))
   -> Either e ()
  rolle = rollupError

rollupError
 :: Measure m (Value (DynCpts e (m a)))
 => Value (DynCpts e (m a))
 -> Either e ()
rollupError
  = go
  where
  go
    = \case
      Block (Components (Extend _ (Left e)))
       -> Left e
          
      Block (Components (Extend _ (Right v)))
       -> go (measure v)
    
      _
       -> Right  ()

valueComponents
 :: MeasureExpr (DynCpts e) b
 => (TypeError -> e)
 -> Value (DynCpts e (Repr b (DynCpts e) a))
 -> DynCpts e (Repr b (DynCpts e) a)
valueComponents throwe
  = \case
    Null
     -> Components
          (Extend Map.empty (Right emptyRepr))
    
    Block f
     -> f
    
    Number d
     -> throwDyn (throwe (NoNumberSelf d))
    
    Text t
     -> throwDyn (throwe (NoTextSelf t))
    
    Bool b
     -> throwDyn (throwe (NoBoolSelf b))

checkExpr
 :: MeasureExpr (DynCpts DynError) b
 => Repr () (Multi Identity)
      (VarName Ident Ident (Import Ident))
 -> ([StaticError], Repr b (DynCpts DynError) Void)
checkExpr m
  = bitransverseRepr
      (fmap (mapError StaticError)
       ... checkMulti
            (DefnError
              . OlappedMatch
              . Text.unpack))
      (checkVar ScopeError)
      m
 <&> \ m -> m >>= throwRepr . StaticError

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
      (displayDyn displayDynError displayExpr)
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
