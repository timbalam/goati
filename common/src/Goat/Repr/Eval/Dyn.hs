{-# LANGUAGE ScopedTypeVariables, LambdaCase, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, FlexibleContexts, RankNTypes, DeriveFunctor, DeriveFoldable, DeriveTraversable, TypeFamilies, OverloadedStrings #-}
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
import Goat.Lang.Parser
  ( IDENTIFIER, CanonPath, CanonSelector
  , parseIdentifier
  )
import Goat.Lang.Class ((#.))
import Goat.Util ((<&>), (...))
import Control.Applicative (liftA2)
import Control.Monad (ap, join)
import Control.Monad.Trans (lift)
import Data.Align (align)
import Data.Bifunctor (bimap, first)
import Data.Bifoldable (bifoldMap)
import Data.Function (on)
import Data.Functor (($>))
import Data.List (intersperse, foldl')
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromMaybe, catMaybes)
import Data.Semigroup ((<>))
import qualified Data.Text as Text
import Data.These (These(..))
import Data.Void (Void)
import Bound (instantiate, (>>>=))
import Prelude.Extras (Eq1(..), Show1(..))


-- | Unrolled expression
data Eval f
  = Eval (Value (f (Repr f (Eval f) Void)))

bindHoles
 :: MeasureExpr (DynCpts e Ident) v
 => (TypeError -> e)
 -> Expr
      (DynCpts e Ident)
      (Repr (DynCpts e Ident) v)
      a
 -> Expr
      (DynCpts e Ident)
      (Repr (DynCpts e Ident) v)
      Void
bindHoles throwe f
  = f >>>= \_ -> throwRepr (throwe Hole)

type MemoRepr 
  = Repr
      (DynCpts DynError Ident)
      (Eval (DynCpts DynError Ident))

instance
  MeasureExpr
    (DynCpts DynError Ident)
    (Eval (DynCpts DynError Ident)) 
  where
  measureExpr f
    = Eval (eval TypeError (bindHoles TypeError f))

instance
  Measure
    (Memo f (Eval (DynCpts DynError Ident)))
    (Value
      (DynCpts DynError Ident
        (Repr (DynCpts DynError Ident)
          (Eval (DynCpts DynError Ident))
          Void)))
  where
  measure (Memo (Eval v) _) = v

instance
  Measure
    (Memo 
      (Expr (DynCpts DynError Ident)
        (Repr (DynCpts DynError Ident) ()))
      ())
    (Value 
      (DynCpts DynError Ident
        (Repr (DynCpts DynError Ident) () Void)))
  where
  measure (Memo _ f)
    = eval TypeError (bindHoles TypeError f)

decompose
 :: ( MeasureExpr (DynCpts e Ident) v
    , Measure
        (Memo
          (Expr
            (DynCpts e Ident)
            (Repr (DynCpts e Ident) v))
          v)
        (Value
          (DynCpts e Ident
            (Repr (DynCpts e Ident) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> DynCpts e Ident a
 -> Repr (DynCpts e Ident) v Void
 -> [Repr (DynCpts e Ident) v Void]
decompose throwe ~(DynCpts pkv pme) m
  = bifoldMap
      pure
      pure
      (Extend
        (selectComponents throwe
          pkv
          (valueComponents throwe (measureRepr m)))
        (maybe
          (getRemaining throwe pkv m)
          throwRepr
          pme))
  
selectComponents
 :: MeasureExpr (DynCpts e Ident) v
 => (TypeError -> e)
 -> Map Ident (Either e b)
 -> DynCpts e Ident (Repr (DynCpts e Ident) v Void)
 -> Map Ident (Repr (DynCpts e Ident) v Void)
selectComponents
  throwe pkv (DynCpts mkv mme)
  = leftOuter pkv mkv
  where
  leftOuter
    = Map.mergeWithKey 
        (\ _ ep em
         -> Just (either throwRepr id (ep >> em)))
        (Map.mapWithKey
          (\ n _ -> throwRepr (err n)))
        (const Map.empty)
  err n
    = fromMaybe
        (throwe (NotComponent (fromIdent n))) mme

throwRepr
 :: MeasureExpr (DynCpts e a) v
 => e -> Repr (DynCpts e a) v b
throwRepr e = wrapComponents (throwDyn e)

wrapComponents
 :: Measure (Expr f (Repr f v)) v
 => f (Scope (Super Int)
        (Scope (Public Ident) (Repr f v)) a)
 -> Repr f v a
wrapComponents c
  = Repr (Comp (memo (Ext (Define c) emptyRepr)))

getRemaining
 :: ( MeasureExpr (DynCpts e Ident) v
    , Measure
        (Memo
          (Expr (DynCpts e Ident)
            (Repr (DynCpts e Ident) v))
          v)
        (Value
          (DynCpts
            e Ident (Repr (DynCpts e Ident) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Map Ident b
 -> Repr (DynCpts e Ident) v Void
 -> Repr (DynCpts e Ident) v Void
getRemaining throwe kv (Repr v)
  = either
      throwRepr
      (\ v -> Repr (v >>= fmap (memo . (`id` kv))))
      (traverse
        (simplify throwe deleteExt . unmemo)
        v)
  where
  deleteExt bs ev
    = pure
        (Comp
          (deleteComponents bs
            (\ kv
             -> either
                  throwRepr
                  (Repr . fmap (memo . (`id` kv)))
                  ev)))
    

deleteComponents
 :: Bindings (DynCpts e Ident) (DynCpts e Ident)
      (Scope (Super Int)
        (Scope (Public Ident)
          (Repr (DynCpts e Ident) v)))
      a
 -> (Map Ident b -> Repr (DynCpts e Ident) v a)
 -> Map Ident b
 -> Expr
      (DynCpts e Ident) (Repr (DynCpts e Ident) v) a
deleteComponents bs f kv = Ext bs' (f kv')
  where
  (kv', bs')
    = transverseBindings
        (\ (DynCpts mkv me)
         -> ( maybe
                (kv `Map.difference` mkv)
                (\_ -> Map.empty)
                me
            , DynCpts (mkv `Map.difference` kv) me
            ))
        bs

getDyn
 :: forall e v a
  . MeasureExpr (DynCpts e Ident) v
 => (TypeError -> e)
 -> DynCpts e Ident (Repr (DynCpts e Ident) v a)
 -> Ident
 -> Repr (DynCpts e Ident) v a
getDyn throwe ~(DynCpts kv me) = get
  where
  get :: Ident -> Repr (DynCpts e Ident) v a
  get n
    = Map.findWithDefault
        (err n)
        n
        (either throwRepr id <$> kv)
  
  err :: Ident -> Repr (DynCpts e Ident) v a
  err n
    = throwRepr
        (fromMaybe
          (throwe (NotComponent (fromIdent n)))
          me)

eval
 :: ( MeasureExpr (DynCpts e Ident) v
    , Measure
        (Memo
          (Expr
            (DynCpts e Ident)
            (Repr (DynCpts e Ident) v))
          v)
        (Value
          (DynCpts
            e Ident (Repr (DynCpts e Ident) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Expr
      (DynCpts e Ident)
      (Repr (DynCpts e Ident) v)
      Void
 -> Value
      (DynCpts
        e Ident (Repr (DynCpts e Ident) v Void))
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
 :: ( MeasureExpr (DynCpts e Ident) v
    , Measure
        (Memo
          (Expr
            (DynCpts e Ident)
            (Repr (DynCpts e Ident) v))
          v)
        (Value
          (DynCpts
            e Ident (Repr (DynCpts e Ident) v Void)))
     -- debug
    , Show e
    )
 => (TypeError -> e)
 -> (Scope
      (Public Ident) (Repr (DynCpts e Ident) v) Void
     -> Repr (DynCpts e Ident) v Void)
 -> Bindings
      (DynCpts e Ident) (DynCpts e Ident)
      (Scope (Super Int)
        (Scope (Public Ident)
          (Repr (DynCpts e Ident) v)))
      Void
 -> DynCpts e Ident (Repr (DynCpts e Ident) v Void)
 -> DynCpts e Ident (Repr (DynCpts e Ident) v Void)
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
  
  ms
    = case c' of
      DynCpts kv _ 
       -> foldMap pure
            (selectComponents
              throwe (kv $> pure ()) c)
  
  substSuper
    = instantiate (\ (Super i) -> lift (ms !! i))

extendComponents
 :: Ord a
 => DynCpts e a b -> DynCpts e a b -> DynCpts e a b
extendComponents
  (DynCpts kv Nothing) (DynCpts nkv nmem)
  = DynCpts (Map.union kv nkv) nmem
extendComponents c _ = c

memoSimplify
 :: ( MeasureExpr (DynCpts e Ident) v
    , Measure
        (Memo
          (Expr
            (DynCpts e Ident)
            (Repr (DynCpts e Ident) v))
          v)
        (Value
          (DynCpts e Ident
            (Repr (DynCpts e Ident) v Void)))
    -- debug
    , Show e
    )
 => (TypeError -> e)
 -> Repr (DynCpts e Ident) v Void
 -> Repr (DynCpts e Ident) v Void
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
        (Value (DynCpts e Ident (Repr f v Void)))
    -- debug
    , Traversable f, Show1 f, Show e
    )
 => (TypeError -> e)
 -> (Bindings
      f f
      (Scope (Super Int)
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
          DynCpts kv me
            = valueComponents throwe (measureRepr m)
          err
            = fromMaybe
                (throwe
                  (NotComponent (fromIdent n)))
                me
          in
          case
          Map.findWithDefault (Left err) n kv
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
        (Value (DynCpts e Ident (Repr f v Void)))
   => Repr f v Void -> Either e Double
  toNum m
    = case
      measureRepr m
       :: Value (DynCpts e Ident (Repr f v Void))
      of
      Number n -> Right n
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotNumber)
  fromNum = fmap Number
  
  toBool
   :: Measure
        (Memo (Expr f (Repr f v)) v)
        (Value (DynCpts e Ident (Repr f v Void)))
   => Repr f v Void -> Either e Bool
  toBool m
    = case
      measureRepr m
       :: Value (DynCpts e Ident (Repr f v Void))
      of
      Bool b -> Right b
      Comp (DynCpts _ (Just e)) -> Left e
      _ -> Left (throwe NotBool)
  fromBool = fmap Bool

valueComponents
 :: (TypeError -> e)
 -> Value (DynCpts e a b)
 -> DynCpts e a b
valueComponents throwe
  = \case
    Null -> DynCpts Map.empty Nothing
    Comp f -> f
    Number d -> throwDyn (throwe (NoNumberSelf d))
    Text t -> throwDyn (throwe (NoTextSelf t))
    Bool b -> throwDyn (throwe (NoBoolSelf b))


--

checkExpr
 :: MeasureExpr (DynCpts DynError Ident) v
 => Repr
      (AnnDefns
        [View (Trail Ident)]
        [Trail Ident]
        (AnnCpts [Ident])
        Ident)
      ()
      (VarName Ident Ident (Import Ident))
 -> ( [StaticError]
    , Repr (DynCpts DynError Ident) v Void
    )
checkExpr m
  = bitransverseRepr
      (\ f c
       -> mapError StaticError
       <$> checkReprComponents f c)
      (checkVar ScopeError)
      m
 <&> (>>= throwRepr . StaticError)
  where
  checkReprComponents
   :: (a -> ([StaticError], b))
   -> AnnDefns
        [View (Trail Ident)]
        [Trail Ident]
        (AnnCpts [Ident])
        Ident
        a
   -> ([StaticError], DynCpts StaticError Ident b)
  checkReprComponents f
    = \case
      Tag (Left (Tag (Left (Declares c))))
       -> checkComponents
            (DefnError
              . OlappedDeclare
              . map fromViewTrails) f c
      
      Tag (Left (Tag (Right (Matches c))))
       -> checkComponents 
            (DefnError
              . OlappedMatch
              . map fromTrail) f c
      
      Tag (Right c)
       -> checkComponents
            (DefnError
              . DuplicateImports
              . map fromIdent) f c
    {-
    where
    trailToSelector (n :| ns)
      = go n ns ""
      where
      go n [] s = s #. fromIdent n
      go n (n':ns) s = go n' ns (s #. fromIdent n)
    viewTrailsToPath
      = \case
        Tag (Left (Local (n :| [])))
         -> fromIdent n
        
        Tag (Left (Local (n :| n' : ns)))
         -> go n' ns (fromIdent n)
        
        Tag (Right (Public (n :| ns)))
         -> go n ns ""
      where
      go n [] s = s #. fromIdent n
      go n (n':ns) s = go n' ns (s #. fromIdent n)
      -}

checkVar
 :: (ScopeError -> e)
 -> VarName Ident Ident (Import Ident)
 -> ([e], e)
checkVar throwe n
  = ([e], e)
  where
  e
    = case n of
      Left (Left (Local n))
       -> throwe
            (NotDefinedLocal(fromIdent n))
      
      Left (Right (Public n))
       -> throwe
            (NotDefinedPublic (fromIdent n))
      
      Right (Import n)
       -> throwe (NotModule (fromIdent n))

-- Print --

displayExpr
 :: forall f v
  . Measure
      (Memo (Expr f (Repr f v)) v)
      (Value
        (DynCpts DynError Ident (Repr f v Void)))
 => Repr f v Void
 -> String
displayExpr m
  = displayValue
      (displayDynCpts displayDynError showIdent)
      (measureRepr m
       :: Value
            (DynCpts DynError Ident (Repr f v Void)))


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
