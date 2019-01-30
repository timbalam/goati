{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

-- | This module along with 'Goat.Expr.Dyn' implement core data representations.
-- The 'Repr' type in this module represent a "higher order abstract syntax" (HOAS) encoding of a Goat value,
-- and is designed to be more suitable for evaluation.
-- This type can be directly instantiated from the typeclass-encoded syntax described in 'Goat.Syntax.Class',
-- or can be converted from the types in 'Goat.Expr.Dyn' after optimisation.
module Goat.Eval.Dyn
  ( Repr(..), Value(..), Self, self, fromSelf
  , Res, Eval, eval, checkEval, runRes, runEval
  , Synt(..)
  , displayValue, displayDyn'
  , match, dynLookup, dynConcat
  , typee, checke
  , S.Ident
  , module Goat.Dyn.DynMap
  , getSelf, handleEnv, escape, handleUse
  )
  where
  
import Goat.Error
import qualified Goat.Syntax.Class as S
import qualified Goat.Syntax.Syntax as P
import Goat.Syntax.Patterns
import Goat.Syntax.Parser (showIdent)
import Goat.Dyn.DynMap
import Goat.Util ((<&>), traverseMaybeWithKey, withoutKeys,
  Compose(..))
import Control.Applicative (liftA2, liftA3, (<|>))
import Control.Monad.Trans.Free
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Comonad.Cofree
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce
import Data.Functor.Identity
import Data.List (elemIndex, nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..), Last(..))
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Tuple (swap)
import Prelude.Extras
  
newtype Repr f = Repr
  { getRepr :: Value (Repr f -> f (Repr f)) }

instance Show (Repr f) where
  showsPrec d (Repr v) = showParen (d > 10)
    (showString "Repr "
      . showsPrec 11 v')
      where
        v' = (fmap . const) (undefined :: ()) v
  
instance Eq (Repr f) where
  Repr v == Repr v' = toUndef v == toUndef v'
    where
      toUndef = (fmap . const) (undefined :: ())

data Value a =
    Block a
  | Number Double
  | Text Text
  | Bool Bool
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
type Self f = Value (f (Repr f))

fromSelf :: (Functor f) => Self f -> Repr f
fromSelf = Repr . fmap const

self :: (Functor f) => Repr f -> Self f
self (Repr v) = v <&> (`id` Repr v)


newtype Synt m a = Synt { readSynt :: m a }

type Res k = ReaderT
  ([S.Ident], [[S.Ident]])
  (Writer [StaticError k])

runRes :: Res k a -> [S.Ident] -> [[S.Ident]] -> ([StaticError k], a)
runRes m r en = (swap . runWriter) (runReaderT m (r, en))

type Eval f = Reader ([Repr f], [([Repr f], Repr f)]) (Repr f)

runEval :: Eval f -> [Repr f] -> [([Repr f], Repr f)] -> Repr f
runEval m r en = runReader m (r, en)

eval
  :: Applicative f
  => Synt (Res k) (Eval (Dyn k f))
  -> ([StaticError k], Self (Dyn k f))
eval (Synt m) = runRes m' [] []
  where
    m' = m <&> (\ ev ->
      self (runEval ev [] []))
    
checkEval
  :: Applicative f
  => Synt (Res k) (Eval (Dyn k f))
  -> Either [StaticError k] (Self (Dyn k f))
checkEval m = case eval m of
  ([], v) -> Right v
  (es, _) -> Left es
  
      
nume = error "Num (Value a)"

instance Num (Value a) where
  fromInteger = Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
  
instance Num (Repr f) where
  fromInteger i = Repr (fromInteger i)
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
instance Num (Synt (Res k) (Eval f)) where
  fromInteger i = Synt (pure (pure (fromInteger i)))
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Value a)"

instance Fractional (Value a) where
  fromRational = Number . fromRational
  (/) = frace
  
instance Fractional (Repr f) where
  fromRational r = Repr (fromRational r)
  (/) = frace
  
instance Fractional (Synt (Res k) (Eval f)) where
  fromRational r = Synt (pure (pure (fromRational r)))
  (/) = frace
  
instance IsString (Value a) where
  fromString = Text . fromString
  
instance IsString (Repr f) where
  fromString s = Repr (fromString s)
  
instance IsString (Synt (Res k) (Eval f)) where
  fromString s = Synt (pure (pure (fromString s)))
  
instance (Applicative f, Foldable f)
  => S.ArithB_ (Value (Dyn k f a)) where
  (#+) = n2n2n (+)
  (#-) = n2n2n (-)
  (#*) = n2n2n (*)
  (#/) = n2n2n (/)
  (#^) = n2n2n (**)
  
instance (Applicative f, Foldable f)
 => S.CmpB_ (Value (Dyn k f a)) where
  (#>)  = n2n2b (>) 
  (#<)  = n2n2b (<)
  (#==) = n2n2b (==)
  (#!=) = n2n2b (/=)
  (#>=) = n2n2b (>=)
  (#<=) = n2n2b (<=)
      
instance (Applicative f, Foldable f)
 => S.LogicB_ (Value (Dyn k f a)) where
  (#||) = b2b2b (||)
  (#&&) = b2b2b (&&)
    
n2n2n f (Number d) (Number d') = Number (d `f` d')
n2n2n _ v          v'          = maybe (typee NotNumber)
  (Block . throwDyn)
  (checke v <|> checke v')
    
n2n2b f (Number d) (Number d') = Bool (d `f` d')
n2n2b _ v          v'          = maybe (typee NotNumber)
  (Block . throwDyn)
  (checke v <|> checke v')
    
b2b2b f (Bool b) (Bool b') = Bool (b `f` b')
b2b2b _ v        v'        = maybe (typee NotBool)
  (Block . throwDyn)
  (checke v <|> checke v')

checke :: Foldable f => Value (Dyn k f a) -> Maybe (DynError k)
checke (Block (Compose m)) = getLast (foldMap (Last . checke') m)
  where
    checke' (Compose (DynMap e kv)) | M.null kv = e
    checke' _                                   = Nothing
checke _                   = Nothing
    
typee :: Applicative f => TypeError k -> Value (Dyn k f a)
typee = Block . throwDyn . TypeError
      
instance (Applicative f, Foldable f)
  => S.Unop_ (Value (Dyn k f a)) where
  neg_ (Number d) = Number (negate d)
  neg_ v          = maybe (typee NotNumber)
    (Block . throwDyn)
    (checke v)
  
  not_ (Bool b) = Bool (not b)
  not_ v        = maybe (typee NotBool)
    (Block . throwDyn)
    (checke v)

reprUnop
 :: (Foldable f, Applicative f)
 => ( Value (Dyn k f (Repr (Dyn k f)))
   -> Value (Dyn k f (Repr (Dyn k f)))
    )
 -> Repr (Dyn k f) -> Repr (Dyn k f)
reprUnop f r = fromSelf (f (self r))

reprBinop
 :: (Foldable f, Applicative f)
 => ( Value (Dyn k f (Repr (Dyn k f)))
   -> Value (Dyn k f (Repr (Dyn k f)))
   -> Value (Dyn k f (Repr (Dyn k f)))
    )
 -> Repr (Dyn k f) -> Repr (Dyn k f) -> Repr (Dyn k f)
reprBinop f r r' = fromSelf (f (self r) (self r'))
    
instance (Foldable f, Applicative f)
 => S.ArithB_ (Repr (Dyn k f)) where
  (#+) = reprBinop (S.#+)
  (#-) = reprBinop (S.#-)
  (#*) = reprBinop (S.#*)
  (#/) = reprBinop (S.#/)
  (#^) = reprBinop (S.#^)
  
instance (Foldable f, Applicative f)
 => S.CmpB_ (Repr (Dyn k f)) where
  (#==) = reprBinop (S.#==)
  (#!=) = reprBinop (S.#!=)
  (#<)  = reprBinop (S.#<)
  (#<=) = reprBinop (S.#<=)
  (#>)  = reprBinop (S.#>)
  (#>=) = reprBinop (S.#>=)
  
instance (Foldable f, Applicative f)
 => S.LogicB_ (Repr (Dyn k f)) where
  (#||) = reprBinop (S.#||)
  (#&&) = reprBinop (S.#&&)
  
instance (Foldable f, Applicative f)
 => S.Unop_ (Repr (Dyn k f)) where
  neg_ = reprUnop S.neg_
  not_ = reprUnop S.not_
    
syntUnop
 :: (Repr (Dyn k f) -> Repr (Dyn k f))
 -> Synt (Res k) (Eval (Dyn k f))
 -> Synt (Res k) (Eval (Dyn k f))
syntUnop f (Synt m) = Synt (fmap (fmap f) m)

syntBinop
 :: (Repr (Dyn k f) -> Repr (Dyn k f) -> Repr (Dyn k f))
 -> Synt (Res k) (Eval (Dyn k f))
 -> Synt (Res k) (Eval (Dyn k f))
 -> Synt (Res k) (Eval (Dyn k f))
syntBinop f (Synt m) (Synt m') = Synt (liftA2 (liftA2 f) m m')
    
instance (Foldable f, Applicative f)
 => S.ArithB_ (Synt (Res k) (Eval (Dyn k f))) where
  (#+) = syntBinop (S.#+)
  (#-) = syntBinop (S.#-)
  (#*) = syntBinop (S.#*)
  (#/) = syntBinop (S.#/)
  (#^) = syntBinop (S.#^)
  
instance (Foldable f, Applicative f)
 => S.CmpB_ (Synt (Res k) (Eval (Dyn k f))) where
  (#==) = syntBinop (S.#==)
  (#!=) = syntBinop (S.#!=)
  (#>)  = syntBinop (S.#>)
  (#>=) = syntBinop (S.#>=)
  (#<)  = syntBinop (S.#<)
  (#<=) = syntBinop (S.#<=)
  
instance (Foldable f, Applicative f)
 => S.LogicB_ (Synt (Res k) (Eval (Dyn k f))) where
  (#||) = syntBinop (S.#||)
  (#&&) = syntBinop (S.#&&)
  
instance (Foldable f, Applicative f)
 => S.Unop_ (Synt (Res k) (Eval (Dyn k f))) where
  neg_ = syntUnop S.neg_
  not_ = syntUnop S.not_

instance Applicative f
  => S.Local (Value (Dyn k f a)) where
  local_ n = (Block 
    . throwDyn
    . StaticError
    . ScopeError)
      (NotDefined n)

indexWhere :: (a -> Maybe b) -> [a] -> Maybe (Int, b)
indexWhere p xs = go xs 0 where
  go (x:xs) i | Just b <- p x = Just (i, b)
              | otherwise     = go xs (i+1)
  go []     i                 = Nothing

handleEnv
  :: S.Ident -> [[S.Ident]] -> Maybe ([([x], c)] -> x)
handleEnv n ns = indexWhere (elemIndex n) ns
    <&> (\ (i, j) scopes -> fst (scopes !! i) !! j)
    
getSelf
  :: Applicative f
  => [([a], Repr (Dyn k f))]
  -> Repr (Dyn k f)
getSelf []        = r0 where 
  r0 = (Repr . Block . const . dyn) (DynMap Nothing M.empty)
getSelf ((_,r):_) = r

instance 
  Applicative f => S.Local (Synt (Res k) (Eval (Dyn k f))) where
  local_ n = Synt (asks (handleEnv n . snd)
    >>= maybe
      (tell [e] >> (return
        . pure
        . Repr
        . Block
        . const
        . throwDyn)
          (StaticError e))
      (\ f -> return (reader (f . snd))))
    where
      e = ScopeError (NotDefined n)

instance (S.Self k, Applicative f)
  => S.Self (Value (Dyn k f a)) where
  self_ n = (Block
    . throwDyn
    . TypeError
    . NotComponent) (S.self_ n)

instance (S.Self k, Ord k, Foldable f, Applicative f)
  => S.Self (Eval (Dyn k f)) where
  self_ n = asks (getSelf . snd) <&> (S.#. n)
    
instance (S.Self k, Ord k, Foldable f, Applicative f)
  => S.Self (Synt (Res k) (Eval (Dyn k f))) where
  self_ n = Synt (pure (S.self_ n))
  
instance Applicative f => S.Extern_ (Value (Dyn k f a)) where
  use_ n = (Block
    . throwDyn
    . StaticError
    . ScopeError)
      (NotModule n)

handleUse :: S.Ident -> [S.Ident] -> Maybe ([x] -> x)
handleUse n ns =
  fmap (\ i mods -> mods !! i) (elemIndex n ns)

instance Applicative f => S.Extern_ (Synt (Res k) (Eval (Dyn k f))) where
  use_ n = Synt (asks (handleUse n . fst)
    >>= maybe
      (tell [e] >> (return 
        . pure
        . Repr
        . Block
        . const
        . throwDyn)
          (StaticError e))
      (\ f -> return (reader (f . fst))))
    where 
      e = ScopeError (NotModule n)
      
instance (S.Self k, Ord k, Foldable f, Applicative f)
  => S.Field_ (Repr (Dyn k f)) where
  type Compound (Repr (Dyn k f)) =
    Repr (Dyn k f)
  r #. n = self r `dynLookup` S.self_ n

instance (S.Self k, Ord k, Foldable f, Applicative f)
  => S.Field_ (Synt (Res k) (Eval (Dyn k f))) where
  type Compound (Synt (Res k) (Eval (Dyn k f))) =
    Synt (Res k) (Eval (Dyn k f))
  Synt m #. n = Synt (m <&> fmap (S.#. n))
  
escape
  :: (MonadReader (q, [r]) m, MonadReader (q', [r']) n)
  => m (n a) -> m (n a)
escape m = fmap (local drop1Snd) (local drop1Snd m) where
  drop1Snd :: (a, [b]) -> (a, [b])
  drop1Snd (a, []  ) = (a, [])
  drop1Snd (a, _:xs) = (a, xs)
  
instance S.Esc (Synt (Res k) (Eval (Dyn k f))) where
  type Lower (Synt (Res k) (Eval (Dyn k f))) = Synt (Res k) (Eval (Dyn k f))
  esc_ (Synt m) = Synt (escape m)
  
instance 
  (S.Self k, Ord k, Foldable f, Applicative f)
 => S.Block_ (Synt (Res k) (Eval (Dyn k f))) where
  type Stmt (Synt (Res k) (Eval (Dyn k f))) =
    Stmt [P.Vis (Path k) (Path k)]
      ( Patt (Matches k) Bind
      , Synt (Res k) (Eval (Dyn k f))
      )
      
  block_ rs = Synt (liftA3 evalBlock
    (dynCheckVis v)
    (local (\ (xs, nns) -> (xs, ns':nns)) (traverse
      (bitraverse dynCheckPatt readSynt)
      pas))
    (asks snd) <&> reader)
    where
      (v, pas) = buildVis rs
      ns' = nub (foldMap (\ (Stmt (ps, _)) -> map name ps) rs)
      
      name :: P.Vis (Path k) (Path k) -> S.Ident
      name (P.Pub (Path n _)) = n
      name (P.Priv (Path n _)) = n
      
      evalBlock (Vis{private=l,public=s}) pas ns (mods, scopes) =
        (Repr . Block) (\ se -> 
          (fmap (values se !!)
          . dyn)
            (DynMap Nothing s))
        where
          values :: Repr (Dyn k f) -> [Repr (Dyn k f)]
          values se = vs
            where
              vs = runReader
                (matched
                  (map (\ (p, fa) -> match p <$> fa) pas))
                (mods, scopes')
             
              en' = localenv se vs
              scopes' = (en',se):scopes
            
          localenv
            :: Repr (Dyn k f)
            -> [Repr (Dyn k f)]
            -> [Repr (Dyn k f)]
          localenv se vs = en' where
            en' = map
              (\ n -> M.findWithDefault
                (self se `dynLookup` S.self_ n)
                n
                lext)
              ns'
              
            -- extend inherited local bindings
            lext = M.mapWithKey
              (\ n m -> case runFree (fmap (vs!!) m) of
                Pure e -> e
                Free dkv -> (maybe 
                  id
                  (\ r -> dynConcat (r scopes))
                  (handleEnv n ns)
                  . Repr . Block . const) (dyn dkv))
              l
      
instance (Ord k, Applicative f) => S.Extend_ (Repr (Dyn k f)) where
  type Ext (Repr (Dyn k f)) = Repr (Dyn k f)
  (#) = dynConcat
      
instance (Ord k, Applicative f) 
  => S.Extend_ (Synt (Res k) (Eval (Dyn k f))) where
  type Ext (Synt (Res k) (Eval (Dyn k f))) =
    Synt (Res k) (Eval (Dyn k f))
   
  Synt m # Synt m' = Synt (liftA2 (liftA2 (S.#)) m m')


dynNumber _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynText _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynBool _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
  
dynRepr
  :: Applicative f
  => Repr (Dyn k f)
  -> Repr (Dyn k f)
  -> Dyn k f (Repr (Dyn k f))
dynRepr (Repr v) = case v of
  Block k  -> k
  Number d -> dynNumber d
  Text t   -> dynText t
  Bool b   -> dynBool b
  
dynSelf
  :: Applicative f
  => Self (Dyn k f)
  -> Dyn k f (Repr (Dyn k f))
dynSelf v = case v of 
  Block m   -> m
  Number d  -> dynNumber d (Number d)
  Text t    -> dynText t (Text t)
  Bool b    -> dynBool b (Bool b)

  
displayValue
  :: (a -> String) -> Value a -> String
displayValue displayBlock v = case v of
  Number d -> show d
  Text t   -> unpack t
  Bool b   ->
    "<bool: " ++ if b then "true" else "false" ++ ">"
  Block a -> displayBlock a


displayDyn' :: Dyn' S.Ident a -> String
displayDyn' = displayDyn . runDyn'

displayDyn :: DynMap S.Ident a -> String
displayDyn (DynMap e kv) =
  case (M.keys kv, e) of
    ([], Nothing) -> "<no components>"
    ([], Just e)  -> "<" ++ displayDynError e ++ ">"
    (ks, mb)      -> "<components: "
      ++ show (map (\ k -> showIdent k "") ks)
      ++ maybe "" (\ e -> " and " ++ displayDynError e) mb
      ++ ">"


dynLookup
  :: (Ord k, Foldable f, Applicative f)
  => Self (Dyn k f) -> k -> Repr (Dyn k f)
dynLookup v k = 
  (either
    (Repr
    . Block
    . const
    . throwDyn)
    id
  . fromMaybe (Left (TypeError (NotComponent k)))
  . getAlt
  . foldMap (Alt . dynLookup')
  . getCompose) (dynSelf v)
  where
    dynLookup' (Compose (DynMap e kv)) = maybe
      (Left <$> e)
      (\ m -> case runFree m of
        Pure r -> Just (Right r)
        Free dkv -> (Just
          . Right
          . Repr
          . Block
          . const)
            (dyn dkv))
      (M.lookup k kv)
      
      
dynConcat
  :: (Ord k, Applicative f) 
  => Repr (Dyn k f)
  -> Repr (Dyn k f)
  -> Repr (Dyn k f)
dynConcat r r' = (Repr . Block) (\ se -> 
  unionWith zip 
    (dynRepr r se)
    (dynRepr r' se))
  where
    zip
      :: (Ord k, Applicative f)
      => Free (DynMap k) (Repr (Dyn k f))
      -> Free (DynMap k) (Repr (Dyn k f))
      -> Free (DynMap k) (Repr (Dyn k f))
    zip m m' = free (zip' (runFree m) (runFree m'))
    
    zip'
      :: (Ord k, Applicative f)
      => FreeF
        (DynMap k)
        (Repr (Dyn k f))
        (Free (DynMap k) (Repr (Dyn k f)))
      -> FreeF
        (DynMap k)
        (Repr (Dyn k f))
        (Free (DynMap k) (Repr (Dyn k f)))
      -> FreeF
        (DynMap k)
        (Repr (Dyn k f))
        (Free (DynMap k) (Repr (Dyn k f)))
    zip' _          (Pure a')   = Pure a'
    zip' (Pure a)   (Free dkv') = (Pure . dynConcat a
      . Repr . Block . const) (dyn dkv')
    zip' (Free dkv) (Free dkv') = Free (runDyn'
      (unionWith zip (dyn dkv) (dyn dkv')))
  
  
type Match r = ReaderT r ((,) [r])

match
  :: (Ord k, Foldable f, Applicative f)
  => Patt (Dyn' k) Bind
  -> Repr (Dyn k f) -> [Repr (Dyn k f)]
match (b :< Decomp ds) r = bind (r':xs) xs b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . decompDyn) ds <&> concat)
    r
  
  decompDyn
    :: (Ord k, Foldable f, Applicative f)
    => Dyn' k (Patt (Dyn' k) Bind)
    -> Match (Repr (Dyn k f)) (Repr (Dyn k f))
  decompDyn = decompMap
    . fmap (iter (fmap Just . decompMap))
    . runDyn'
    . fmap liftPatt
    where
      liftPatt p = ReaderT (\ r -> (match p r, Nothing))
    
  decompMap
    :: (Ord k, Foldable f, Applicative f)
    => DynMap k
      (Match (Repr (Dyn k f)) (Maybe (Repr (Dyn k f))))
    -> Match (Repr (Dyn k f)) (Repr (Dyn k f))
  decompMap (DynMap eMatch kvMatch) = ReaderT (\ r ->
    let
      v = self r
      d' = Compose (getCompose (dynSelf v) <&> removeMatched')
    in 
      split v (DynMap eMatch kvMatch) <&> recomb d')
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split v (DynMap e kv) =
        traverseMaybeWithKey 
          (\ k mm ->
            runReaderT mm (v `dynLookup` k))
          kv <&> DynMap e . fmap pure
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb d dkv = (Repr
        . Block
        . const
        . unionWith
          (const id)
          d)
          (dyn dkv)
          
      removeMatched' (Compose (DynMap ee kvv)) =
          (Compose 
            (DynMap
              ee
              (withoutKeys kvv (M.keysSet kvMatch))))
