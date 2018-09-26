{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

module My.Types.Eval
  ( Repr(..), Value(..), Self, self, fromSelf
  , Res, Eval, eval, checkEval
  , throwDyn, DynMap(..), Dyn
  , displayValue, displayDyn
  , dynCheckPatt, dynCheckVis, dynCheckTup
  , match, dynLookup, dynConcat
  , S.Ident
  )
  where
  
import My.Types.Error
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import My.Types.Paths.Rec
import My.Types.Paths.Patt
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
import Prelude.Extras
import Data.List (elemIndex)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Data.Monoid (Endo(..))
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Tuple (swap)
  
newtype Repr f = Repr { getRepr :: Value (Repr f -> f (Repr f)) }

instance Show (Repr f) where
  showsPrec d (Repr v) = showParen (d > 10)
    (showString "Repr " . showsPrec 11 (fmap undefined v :: Value ()))
  
instance Eq (Repr f) where
  Repr v == Repr v' = (fmap undefined v :: Value ()) ==
    (fmap undefined v' :: Value ())

data Value a =
    Block a
  | Number Double
  | Text Text
  | Bool Bool
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
  
type Self f = Value (f (Repr f))

fromSelf :: Functor f => Self f -> Repr f
fromSelf = Repr . fmap const

self :: Functor f => Repr f -> Self f
self (Repr v) = v <&> (`id` Repr v)
  
  
type Res k = ReaderT [S.Ident] (Writer [StaticError k])

runRes :: Res k a -> [S.Ident] -> ([StaticError k], a)
runRes m r = (swap . runWriter) (runReaderT m r)

type Eval f = [Repr f] -> Repr f -> Repr f

  
eval :: Res k (Eval (Dyn k)) -> ([StaticError k], Self (Dyn k))
eval m = runRes (fmap (\ ev -> self (ev [] r0)) m) []
  where
    r0 = (Repr . Block . const . Compose) (DynMap Nothing M.empty)
    
checkEval
  :: Res k (Eval (Dyn k))
  -> Either [StaticError k] (Self (Dyn k))
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
  
instance Num (Res k (Eval f)) where
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
  
  
instance Fractional (Repr f) where
  fromRational r = Repr (fromRational r)
  (/) = frace
  
instance Fractional (Res k (Eval f)) where
  fromRational r = pure (\ _ _ -> fromRational r)
  (/) = frace
  
instance IsString (Value a) where
  fromString = Text . fromString
  
instance IsString (Repr f) where
  fromString s = Repr (fromString s)
  
instance IsString (Res k (Eval f)) where
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
    
instance S.Lit (Repr (Dyn k)) where
  unop_ op r = fromSelf (S.unop_ op (self r))
    
  binop_ op r r' = fromSelf (S.binop_ op
        (self r)
        (self r'))
    
instance S.Lit (Res k (Eval (Dyn k))) where
  unop_ op m = m <&> (\ ev en se -> S.unop_ op (ev en se))
  binop_ op m m' = liftA2 (binop' op) m m' where
    binop' op ev ev' en se = S.binop_ op (ev en se) (ev' en se)
      
instance S.Local (Value (Dyn k a)) where
  local_ n = (Block 
    . throwDyn
    . StaticError
    . ScopeError) (NotDefined n)
  
instance S.Local (Res k (Eval (Dyn k))) where
  local_ n = asks (elemIndex n)
    >>= maybe
      (tell [e] >> return (\ _ _ ->
        (Repr . Block . const
          . throwDyn) (StaticError e)))
      (\ i -> return (\ en _ -> en !! i))
    where 
      e = ScopeError (NotDefined n)
      
instance S.Self k => S.Self (Value (Dyn k a)) where
  self_ n = (Block
    . throwDyn
    . TypeError
    . NotComponent) (S.self_ n)
    
instance (S.Self k, Ord k) => S.Self (Eval (Dyn k)) where
  self_ n = \ _ se -> self se `dynLookup` S.self_ n
    
instance (S.Self k, Ord k) => S.Self (Res k (Eval (Dyn k))) where
  self_ n = pure (S.self_ n)
  

instance (S.Self k, Ord k) => S.Field (Repr (Dyn k)) where
  type Compound (Repr (Dyn k)) = Repr (Dyn k)
  r #. n = self r `dynLookup` S.self_ n

instance (S.Self k, Ord k) => S.Field (Res k (Eval (Dyn k))) where
  type Compound (Res k (Eval (Dyn k))) = Res k (Eval (Dyn k))
  m #. n = m <&> (\ ev en se -> ev en se S.#. S.self_ n)

    
instance (S.Self k, Ord k) => S.Tuple (Res k (Eval (Dyn k))) where
  type Tup (Res k (Eval (Dyn k))) = Tup k (Res k (Eval (Dyn k)))
      
  tup_ ts = dynCheckTup (foldMap (Comps . getTup) ts) <&>
    (\ kv en se ->
      (Repr . Block . const . fmap (\ ev -> ev en se) . Compose)
        (DynMap Nothing kv))
  
instance (S.Self k, Ord k) => S.Block (Res k (Eval (Dyn k))) where
  type Rec (Res k (Eval (Dyn k))) =
    Rec [P.Vis (Path k) (Path k)]
      (Patt (Decomps k) Bind, Res k (Eval (Dyn k)))
      
  block_ rs = liftA3 evalBlock
    (dynCheckVis v)
    (local (ns'++) (traverse
      (bitraverse dynCheckPatt id)
      pas))
    ask
    where
      (v, pas, ns') = buildVis rs
      
      evalBlock (Vis{private=l,public=s}) pas ns en _ = Repr (Block k)
        where
          k :: Repr (Dyn k) -> Dyn k (Repr (Dyn k))
          k se = Compose (DynMap Nothing kv) where
            kv = M.map (fmap (values se!!)) s
            
          values :: Repr (Dyn k) -> [Repr (Dyn k)]
          values se = vs
            where
              vs = foldMap
                (\ (p, ev) ->
                  match p (ev (en' ++ en) se))
                pas
             
              en' = localenv se vs
            
          localenv
            :: S.Self k
            => Repr (Dyn k) -> [Repr (Dyn k)] -> [Repr (Dyn k)]
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
                  . Repr . Block . const) (Compose dkv))
              l
      
instance Ord k => S.Extend (Repr (Dyn k)) where
  type Ext (Repr (Dyn k)) = Repr (Dyn k)
  (#) = dynConcat
      
instance Ord k => S.Extend (Res k (Eval (Dyn k))) where
  type Ext (Res k (Eval (Dyn k))) = Res k (Eval (Dyn k))
   
  (#) = liftA2 ext' where
    ext' evl evr en se = evl en se S.# evr en se


data DynMap k a = DynMap (Maybe (DynError k)) (M.Map k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
instance Show k => Show1 (DynMap k) where
  showsPrec1 = showsPrec
  
instance Eq k => Eq1 (DynMap k) where
  (==#) = (==)
  
type Dyn k = Compose (DynMap k) (Free (DynMap k))
  
unionWith
  :: Ord k
  => (Free (DynMap k) a -> Free (DynMap k) a -> Free (DynMap k) a)
  -> Dyn k a -> Dyn k a -> Dyn k a
unionWith f (Compose (DynMap e kva)) (Compose (DynMap Nothing kvb)) = 
  Compose (DynMap e (M.unionWith f kva kvb))
unionWith _ _ d = d
  
throwDyn :: DynError k -> Dyn k a
throwDyn e = Compose (DynMap (Just e) M.empty)
    
pruneDyn
  :: (a -> Maybe b)
  -> Free (DynMap k) a -> Maybe (Free (DynMap k) b)
pruneDyn f = go where
  go = iter pruneMap . fmap (fmap pure . f)
  
  pruneMap
    :: DynMap k (Maybe (Free (DynMap k) b))
    -> Maybe (Free (DynMap k) b)
  pruneMap (DynMap e kv) =
    maybeWrap (DynMap e (M.mapMaybe id kv))
    
  maybeWrap (DynMap Nothing kv) | M.null kv = Nothing
  maybeWrap d                               = Just (wrap d)

  
dynNumber _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynText _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
dynBool _ = (const . throwDyn) (TypeError NoPrimitiveSelf)
  
dynRepr
  :: Repr (Dyn k) -> Repr (Dyn k) -> Dyn k (Repr (Dyn k))
dynRepr (Repr v) = case v of
  Block k  -> k
  Number d -> dynNumber d
  Text t   -> dynText t
  Bool b   -> dynBool b
  
dynSelf :: Self (Dyn k) -> Dyn k (Repr (Dyn k))
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


dynLookup :: Ord k => Self (Dyn k) -> k -> Repr (Dyn k)
dynLookup v k = maybe 
  ((Repr . Block . const) (throwDyn e'))
  (\ m -> case runFree m of
    Pure r -> r
    Free dkv -> (Repr . Block . const) (Compose dkv))
  (M.lookup k kv)
  where
    Compose (DynMap e kv) = dynSelf v
    e' = fromMaybe (TypeError (NotComponent k)) e
      
      
dynConcat :: Ord k => Repr (Dyn k) -> Repr (Dyn k) -> Repr (Dyn k)
dynConcat r r' = (Repr . Block) (\ se -> unionWith zip
    (dynRepr r se)
    (dynRepr r' se))
  where
    zip m m' = free (zip' (runFree m) (runFree m'))
    
    zip' _          (Pure a')   = Pure a'
    zip' (Pure a)   (Free dkv') = (Pure . dynConcat a
      . Repr . Block . const) (Compose dkv')
    zip' (Free dkv) (Free dkv') = Free (getCompose 
      (unionWith zip (Compose dkv) (Compose dkv')))
  
{- 
type Match r = (,) [r -> r]

match
  :: (S.Self k, Ord k)
  => Patt (Dyn k) Bind
  -> [Repr (Dyn k) -> Repr (Dyn k)]
match (b :< Decomp ds) = bind (f:fs) fs b
  where
  (fs, Endo (Dual f)) =
    foldMap (Endo . Dual) <$> traverse decompDyn ds
  
  decompDyn
    :: (S.Self k, Ord k)
    => Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k)) (Repr (Dyn k) -> Repr (Dyn k))
  decompDyn (Compose dkv) = 
      Repr
        . Block
        . const
        . decompMap
          (fmap (iter (fmap emptyDyn . decompMap)
            . getCompose
            . fmap liftPatt) (Compose dkv))
    where
      liftPatt p = (match p, const Nothing)
      emptyDyn (Compose (DynMap Nothing kv))
        | M.null kv          = Nothing
      emptyDyn (Compose dkv) = Just (Compose dkv)
      
    
  decompMap
    :: (S.Self k, Ord k)
    => DynMap k
      (Match (Repr (Dyn k))
        (Self (Dyn k) -> Maybe (Dyn k (Repr (Dyn k)))))
    -> Match (Repr (Dyn k)) (Self (Dyn k) -> Dyn k (Repr (Dyn k)))
  decompMap (DynMap eMatch kvMatch) = 
    split (DynMap eMatch kvMatch) <&> recomb
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split (DynMap e kv) = DynMap e kv' where
        kv' = traverseMaybeWithKey 
          (\ k m -> bimap 
            (\ f v -> f (self v `dynLookup` k))
            m <&> (\ f -> f (self (v `dynLookup` k)))
          kv
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb dkv v = Compose dkv'
        where
          Compose (DynMap ee kvv) = dynSelf v
          Compose dkv' = unionWith (const id)
            (Compose (DynMap ee (withoutKeys kvv (M.keysSet kvMatch))))
            (Compose (fmap (wrap . getCompose) dkv))
-}
            
type Match r = ReaderT r ((,) [r])

match
  :: (S.Self k, Ord k)
  => Patt (Dyn k) Bind
  -> Repr (Dyn k) -> [Repr (Dyn k)]
match (b :< Decomp ds) r = bind (r':xs) xs b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . decompDyn) ds <&> concat)
    r
  
  decompDyn
    :: (S.Self k, Ord k)
    => Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  decompDyn = decompMap
    . fmap (iter (fmap Just . decompMap))
    . getCompose
    . fmap liftPatt
    where
      liftPatt p = ReaderT (\ r -> (match p r, Nothing))
    
  decompMap
    :: (S.Self k, Ord k)
    => DynMap k
      (Match (Repr (Dyn k)) (Maybe (Repr (Dyn k))))
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  decompMap (DynMap eMatch kvMatch) = ReaderT (\ r ->
    let d = self r in 
    split d (DynMap eMatch kvMatch) <&> recomb d)
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split d (DynMap e kv) =
        traverseMaybeWithKey 
          (\ k m ->
            runReaderT m (d `dynLookup` k))
          kv <&> DynMap e . fmap pure
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb d dkv = (Repr . Block . const) (Compose dkv')
        where
          Compose (DynMap ee kvv) = dynSelf d
          Compose dkv' = unionWith (const id)
            (Compose (DynMap ee (withoutKeys kvv (M.keysSet kvMatch))))
            (Compose dkv)

  
dynCheckNode
  :: Applicative f
  => (k -> ([f a], f (Free (DynMap k) a)) -> f (Free (DynMap k) a))
  -> Node k (f a) -> ([f a], f (Free (DynMap k) a))
dynCheckNode check (Node m) = iterT freeDyn (fmap (fmap pure) m)
  where
    freeDyn = pure . fmap (wrap . DynMap Nothing)
        . M.traverseWithKey check

dynCheckStmts
  :: MonadWriter [StaticError k] f
  => (n -> DefnError k)
  -> n -> ([f b], f (Free (DynMap k) a))
  -> (f (Free (DynMap k) a))
dynCheckStmts throw n pp = case pp of
  ([], m) -> m
  (as, m) -> let e = DefnError (throw n) in
    tell [e] >> m >> sequenceA as >> (return . wrap
      . getCompose
      . throwDyn) (StaticError e)

dynCheckDecomp
  :: MonadWriter [StaticError k] f
  => Decomps k (f a) -> f (Dyn k a)
dynCheckDecomp (Compose (Comps kv)) = Compose . DynMap Nothing <$>
  M.traverseWithKey
    (\ k -> check k . dynCheckNode check)
    kv
  where
    check = dynCheckStmts OlappedMatch

dynCheckPatt
  :: MonadWriter [StaticError k] f
  => Patt (Decomps k) a
  -> f (Patt (Dyn k) a)
dynCheckPatt (a :< Decomp cs) =
  (a :<) . Decomp <$>
    traverse (dynCheckDecomp . fmap dynCheckPatt) cs

dynCheckTup
  :: MonadWriter [StaticError k] f
  => Comps k (Node k (f a))
  -> f (M.Map k (Free (DynMap k) a))
dynCheckTup (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv
  where
    check = dynCheckStmts (OlappedSet . P.Pub)
      
      
dynCheckVis
  :: (S.Self k, Ord k, MonadWriter [StaticError k] f)
  => Vis k (Node k (Maybe a))
  -> f (Vis k (Free (DynMap k) a))
dynCheckVis (Vis{private=l,public=s}) =
  liftA2 prunedVis
    (dynCheckPrivate l)
    (checkVis dupl <*> dynCheckPublic s)
  where
    dupl =
      M.filterWithKey
        (\ n _ -> S.self_ n `M.member` s)
        l
        
    prunedVis l s = Vis
      { private = pruneMap (M.difference l dupl)
      , public = pruneMap s
      }
    
    pruneMap :: M.Map i (Free (DynMap k) (Maybe a))
      -> M.Map i (Free (DynMap k) a)
    pruneMap = M.mapMaybe (pruneDyn id)

      
    dynCheckPrivate
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map S.Ident (Node k a)
      -> f (M.Map S.Ident (Free (DynMap k) a))  
    dynCheckPrivate = M.traverseWithKey
      (\ n -> checkPriv n . dynCheckNode checkPub
        . fmap pure)
      
    dynCheckPublic
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map k (Node k a)
      -> f (M.Map k (Free (DynMap k) a))
    dynCheckPublic = M.traverseWithKey
      (\ k -> checkPub k . dynCheckNode checkPub
        . fmap pure)
      
    checkVis dupl = writer (f, es)
      where
        (Endo f, es) = M.foldMapWithKey
          (\ n _ -> let e = DefnError (OlappedVis n) in
            ((Endo . M.insert (S.self_ n)
              . wrap
              . getCompose
              . throwDyn) (StaticError e), [e]))
          dupl
          
    checkPriv
      :: MonadWriter [StaticError k] f
      => S.Ident -> ([f a], f (Free (DynMap k) a))
      -> f (Free (DynMap k) a)
    checkPriv = dynCheckStmts (OlappedSet . P.Priv)
    
    checkPub
      :: MonadWriter [StaticError k] f
      => k -> ([f a], f (Free (DynMap k) a))
      -> f (Free (DynMap k) a)
    checkPub = dynCheckStmts (OlappedSet . P.Pub)
