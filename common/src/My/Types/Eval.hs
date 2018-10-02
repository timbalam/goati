{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

module My.Types.Eval
  ( Repr(..), Value(..), Self, self, fromSelf
  , Res, Eval, eval, checkEval
  , Repr', Self', Eval'
  , displayValue, displayDyn
  , match, dynLookup, dynConcat
  , S.Ident
  , module My.Types.DynMap
  )
  where
  
import My.Types.Error
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import My.Types.Paths.Rec
import My.Types.Paths.Patt
import My.Types.DynMap
import My.Syntax.Parser (showIdent)
import My.Util ((<&>), traverseMaybeWithKey, withoutKeys,
  Compose(..))
import Control.Applicative (liftA2, liftA3)
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
import Data.List (elemIndex)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..))
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Tuple (swap)
import Prelude.Extras
  
newtype Repr f m = Repr
  { getRepr :: m (Value (Repr f m -> f (Repr f m))) }

instance (Show1 m, Functor m) => Show (Repr f m) where
  showsPrec d (Repr v) = showParen (d > 10)
    (showString "Repr "
      . showsPrec1 11 v')
      where
        v' = (fmap . fmap . const) (undefined :: ()) v
  
instance (Eq1 m, Functor m) => Eq (Repr f m) where
  Repr v == Repr v' = toUndef v ==# toUndef v'
    where
      toUndef = (fmap . fmap . const) (undefined :: ())

data Value a =
    Block a
  | Number Double
  | Text Text
  | Bool Bool
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
type Self f m = Value (f (Repr f m))

fromSelf :: (Functor f, Functor m) => m (Self f m) -> Repr f m
fromSelf = Repr . fmap (fmap const)

self :: (Functor f, Functor m) => Repr f m -> m (Self f m)
self (Repr m) = m <&> \ v -> v <&> (`id` Repr m)


type Res k = ReaderT [S.Ident] (Writer [StaticError k])

runRes :: Res k a -> [S.Ident] -> ([StaticError k], a)
runRes m r = (swap . runWriter) (runReaderT m r)

type Eval f m = [Repr f m] -> Repr f m -> Repr f m


eval
  :: Res k (Eval' (Dyn k))
  -> ([StaticError k], Self' (Dyn k))
eval m =
  runRes (fmap (\ ev -> runIdentity (self (ev [] r0))) m) []
  where
    r0 = (Repr . pure
      . Block
      . const
      . Compose) (DynMap Nothing M.empty)
    
checkEval
  :: Res k (Eval' (Dyn k))
  -> Either [StaticError k] (Self' (Dyn k))
checkEval m = case eval m of
  ([], v) -> Right v
  (es, _) -> Left es
  
type Repr' f = Repr f Identity
type Eval' f = Eval f Identity
type Self' f = Self f Identity
      
nume = error "Num (Value a)"

instance Num (Value a) where
  fromInteger = Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
  
instance Applicative m => Num (Repr f m) where
  fromInteger i = (Repr . pure) (fromInteger i)
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
instance Applicative m => Num (Res k (Eval f m)) where
  fromInteger i = pure (\ _ _ -> fromInteger i)
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
  
  
instance Applicative m => Fractional (Repr f m) where
  fromRational r = (Repr . pure) (fromRational r)
  (/) = frace
  
instance Applicative m => Fractional (Res k (Eval f m)) where
  fromRational r = pure (\ _ _ -> fromRational r)
  (/) = frace
  
instance IsString (Value a) where
  fromString = Text . fromString
  
instance Applicative m => IsString (Repr f m) where
  fromString s = (Repr . pure) (fromString s)
  
instance Applicative m => IsString (Res k (Eval f m)) where
  fromString s = pure (\ _ _ -> fromString s)
      
instance S.Lit (Value (Dyn k a)) where
  unop_ op v = unop op v where
    unop S.Not (Bool b)   = Bool (not b)
    unop S.Not _          = typee NotBool
    unop S.Neg (Number d) = Number (negate d)
    unop S.Neg _          = typee NotNumber
    
    typee = Block . throwDyn . TypeError
      
  binop_ op v v' = binop op v v' where
    binop S.Add  = n2n2n (+)
    binop S.Sub  = n2n2n (-)
    binop S.Prod = n2n2n (*)
    binop S.Div  = n2n2n (/)
    binop S.Pow  = n2n2n (**)
    binop S.Gt   = n2n2b (>) 
    binop S.Lt   = n2n2b (<)
    binop S.Eq   = n2n2b (==)
    binop S.Ne   = n2n2b (/=)
    binop S.Ge   = n2n2b (>=)
    binop S.Le   = n2n2b (<=)
    binop S.Or   = b2b2b (||)
    binop S.And  = b2b2b (&&)
    
    b2b2b f (Bool b) (Bool b') = Bool (b `f` b')
    b2b2b _ _        _         = typee NotBool
    
    n2n2n f (Number d) (Number d') = Number (d `f` d')
    n2n2n _ _          _           = typee NotNumber
    
    n2n2b f (Number d) (Number d') = Bool (d `f` d')
    n2n2b _ _          _           = typee NotNumber
    
    typee = Block . throwDyn . TypeError
    
instance Applicative m => S.Lit (Repr (Dyn k) m) where
  unop_ op r = fromSelf (S.unop_ op <$> self r)
    
  binop_ op r r' = fromSelf (liftA2 (S.binop_ op)
        (self r)
        (self r'))
    
instance Applicative m => S.Lit (Res k (Eval (Dyn k) m)) where
  unop_ op m = m <&> (\ ev en se -> S.unop_ op (ev en se))
  binop_ op m m' = liftA2 (binop' op) m m' where
    binop' op ev ev' en se = S.binop_ op (ev en se) (ev' en se)
      
instance S.Local (Value (Dyn k a)) where
  local_ n = (Block 
    . throwDyn
    . StaticError
    . ScopeError) (NotDefined n)
  
instance Applicative m => S.Local (Res k (Eval (Dyn k) m)) where
  local_ n = asks (elemIndex n)
    >>= maybe
      (tell [e] >> return (\ _ _ ->
        (Repr . pure . Block . const
          . throwDyn) (StaticError e)))
      (\ i -> return (\ en _ -> en !! i))
    where 
      e = ScopeError (NotDefined n)
      
instance S.Self k => S.Self (Value (Dyn k a)) where
  self_ n = (Block
    . throwDyn
    . TypeError
    . NotComponent) (S.self_ n)
    
instance (S.Self k, Ord k, Monad m)
  => S.Self (Eval (Dyn k) m) where
  self_ n = \ _ se -> self se `dynLookup` S.self_ n
    
instance (S.Self k, Ord k, Monad m)
  => S.Self (Res k (Eval (Dyn k) m)) where
  self_ n = pure (S.self_ n)
  

instance (S.Self k, Ord k, Monad m)
  => S.Field (Repr (Dyn k) m) where
  type Compound (Repr (Dyn k) m) = Repr (Dyn k) m
  r #. n = self r `dynLookup` S.self_ n

instance (S.Self k, Ord k, Monad m)
  => S.Field (Res k (Eval (Dyn k) m)) where
  type Compound (Res k (Eval (Dyn k) m)) = Res k (Eval (Dyn k) m)
  m #. n = m <&> (\ ev en se -> ev en se S.#. S.self_ n)

    
instance (S.Self k, Ord k, Monad m)
  => S.Tuple (Res k (Eval (Dyn k) m)) where
  type Tup (Res k (Eval (Dyn k) m)) =
    Tup k (Res k (Eval (Dyn k) m))
      
  tup_ ts = dynCheckTup (foldMap (Comps . getTup) ts) <&>
    (\ kv en se ->
      (Repr . pure
        . Block
        . const
        . fmap (\ ev -> ev en se)
        . Compose)
        (DynMap Nothing kv))
  
instance (S.Self k, Ord k, Monad m)
  => S.Block (Res k (Eval (Dyn k) m)) where
  type Rec (Res k (Eval (Dyn k) m)) =
    Rec [P.Vis (Path k) (Path k)]
      (Patt (Decomps k) Bind, Res k (Eval (Dyn k) m))
      
  block_ rs = liftA3 evalBlock
    (dynCheckVis v)
    (local (ns'++) (traverse
      (bitraverse dynCheckPatt id)
      pas))
    ask
    where
      (v, pas, ns') = buildVis rs
      
      evalBlock (Vis{private=l,public=s}) pas ns en _ =
        (Repr . return) (Block k)
        where
          k :: Repr (Dyn k) m -> Dyn k (Repr (Dyn k) m)
          k se = Compose (DynMap Nothing kv) where
            kv = M.map (fmap (values se!!)) s
            
          values :: Repr (Dyn k) m -> [Repr (Dyn k) m]
          values se = vs
            where
              vs = foldMap
                (\ (p, ev) ->
                  match p (ev (en' ++ en) se))
                pas
             
              en' = localenv se vs
            
          localenv
            :: Repr (Dyn k) m
            -> [Repr (Dyn k) m]
            -> [Repr (Dyn k) m]
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
                Pure r -> r
                Free dkv -> (maybe 
                  id
                  (\ i -> dynConcat (en !! i))
                  (elemIndex n ns)
                  . Repr . return . Block . const) (Compose dkv))
              l
      
instance (Ord k, Applicative m)
  => S.Extend (Repr (Dyn k) m) where
  type Ext (Repr (Dyn k) m) = Repr (Dyn k) m
  (#) = dynConcat
      
instance (Ord k, Applicative m)
  => S.Extend (Res k (Eval (Dyn k) m)) where
  type Ext (Res k (Eval (Dyn k) m)) = Res k (Eval (Dyn k) m)
   
  (#) = liftA2 ext' where
    ext' evl evr en se = evl en se S.# evr en se


dynNumber _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynText _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynBool _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
  
dynRepr
  :: Functor m
  => Repr (Dyn k) m
  -> m (Repr (Dyn k) m -> Dyn k (Repr (Dyn k) m))
dynRepr (Repr m) = m <&> \ v -> case v of
  Block k  -> k
  Number d -> dynNumber d
  Text t   -> dynText t
  Bool b   -> dynBool b
  
dynSelf
  :: Self (Dyn k) m
  -> Dyn k (Repr (Dyn k) m)
dynSelf v = case v of 
  Block (Compose dkv) -> Compose dkv
  Number d            -> dynNumber d (Number d)
  Text t              -> dynText t (Text t)
  Bool b              -> dynBool b (Bool b)

  
displayValue
  :: (a -> String) -> Value a -> String
displayValue displayBlock v = case v of
  Number d -> show d
  Text t   -> unpack t
  Bool b   ->
    "<bool: " ++ if b then "true" else "false" ++ ">"
  Block a -> displayBlock a


displayDyn :: Dyn S.Ident a -> String
displayDyn (Compose (DynMap e kv)) = case (M.keys kv, e) of
  ([], Nothing) -> "<no components>"
  ([], Just e)  -> "<" ++ displayDynError e ++ ">"
  (ks, mb)      -> "<components: "
    ++ show (map (\ k -> showIdent k "") ks)
    ++ maybe "" (\ e -> " and " ++ displayDynError e) mb
    ++ ">"


dynLookup
  :: (Ord k, Monad m)
  => m (Self (Dyn k) m) -> k -> Repr (Dyn k) m
dynLookup m k = Repr (m >>= dynLookup' . dynSelf)
  where
    dynLookup' (Compose (DynMap e kv)) =
      maybe 
        ((return . Block . const . throwDyn) (err e))
        (\ m -> case runFree m of
          Pure r -> getRepr r
          Free dkv -> (return . Block . const) (Compose dkv))
        (M.lookup k kv)
  
    err = fromMaybe (TypeError (NotComponent k))
      
      
dynConcat
  :: (Ord k, Applicative m)
  => Repr (Dyn k) m -> Repr (Dyn k) m -> Repr (Dyn k) m
dynConcat r r' = Repr (liftA2
  (\ k k' -> Block (\ se -> unionWith zip (k se) (k' se)))
  (dynRepr r)
  (dynRepr r'))
  where
    zip m m' = free (zip' (runFree m) (runFree m'))
    
    zip' _          (Pure a')   = Pure a'
    zip' (Pure a)   (Free dkv') = (Pure . dynConcat a
      . Repr . pure . Block . const) (Compose dkv')
    zip' (Free dkv) (Free dkv') = Free (getCompose 
      (unionWith zip (Compose dkv) (Compose dkv')))
  
  
type Match r = ReaderT r ((,) [r])

match
  :: (S.Self k, Ord k, Monad m)
  => Patt (Dyn k) Bind
  -> Repr (Dyn k) m -> [Repr (Dyn k) m]
match (b :< Decomp ds) r = bind (r':xs) xs b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . decompDyn) ds <&> concat)
    r
  
  decompDyn
    :: (S.Self k, Ord k, Monad m)
    => Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k) m) (Repr (Dyn k) m)
  decompDyn = decompMap
    . fmap (iter (fmap Just . decompMap))
    . getCompose
    . fmap liftPatt
    where
      liftPatt p = ReaderT (\ r -> (match p r, Nothing))
    
  decompMap
    :: (S.Self k, Ord k, Monad m)
    => DynMap k
      (Match (Repr (Dyn k) m) (Maybe (Repr (Dyn k) m)))
    -> Match (Repr (Dyn k) m) (Repr (Dyn k) m)
  decompMap (DynMap eMatch kvMatch) = ReaderT (\ r ->
    let m = self r in 
    split m (DynMap eMatch kvMatch) <&> recomb m)
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split m (DynMap e kv) =
        traverseMaybeWithKey 
          (\ k mm ->
            runReaderT mm (m `dynLookup` k))
          kv <&> DynMap e . fmap pure
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb m dkv = Repr (m <&> recomb' . dynSelf)
        where 
          recomb' (Compose (DynMap ee kvv)) =
            (Block . const)
              (unionWith (const id)
                (Compose
                  (DynMap
                    ee
                    (withoutKeys kvv (M.keysSet kvMatch))))
                (Compose dkv))
