{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

module My.Types.Eval
  ( Repr(..), Value(..), Self, Res, Eval, eval, checkEval
  , throwDyn, Dyn(..), Dyns, displayValue, displayDyn)
  where
  
import My.Types.Error
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import My.Types.Paths.Rec
import My.Types.Paths.Patt
import My.Syntax.Parser (showIdent)
import My.Util ((<&>), traverseMaybeWithKey, withoutKeys)
import Control.Applicative (liftA2, liftA3)
import Control.Monad.Trans.Free
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Comonad.Cofree
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Functor.Compose
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
  deriving (Eq, Show, Functor)
  
type Self f = Value (f (Repr f))

fromSelf :: Functor f => Self f -> Repr f
fromSelf = Repr . fmap const

self :: Functor f => Repr f -> Self f
self (Repr v) = v <&> (`id` Repr v)
  
  
type Res k = ReaderT [S.Ident] (Writer [StaticError k])

runRes :: Res k a -> [S.Ident] -> ([StaticError k], a)
runRes m r = (swap . runWriter) (runReaderT m r)

type Eval f = [Repr f] -> Repr f -> Repr f

  
eval :: Res k (Eval (Dyns k)) -> ([StaticError k], Self (Dyns k))
eval m = runRes (fmap (\ ev -> self (ev [] r0)) m) []
  where
    r0 = (Repr . Block . const . Compose) (DynMap Nothing M.empty)
    
checkEval
  :: Res k (Eval (Dyns k))
  -> Either [StaticError k] (Self (Dyns k))
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
  
instance Num (Res k (Eval f)) where
  fromInteger i = pure (\ _ _ -> Repr (fromInteger i))
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
  
instance Fractional (Res k (Eval f)) where
  fromRational r = pure (\ _ _ -> Repr (fromRational r))
  (/) = frace
  
instance IsString (Value a) where
  fromString = Text . fromString
  
instance IsString (Res k (Eval f)) where
  fromString s = pure (\ _ _ -> Repr (fromString s))
      
instance S.Lit (Value (Dyns k a)) where
  unop_ op v = unop op v where
    unop S.Not (Bool b)   = Bool (not b)
    unop S.Not _          = typee NotBool
    unop S.Neg (Number d) = Number (negate d)
    unop S.Neg _          = typee NotNumber
    
    typee = Block . Compose . throwDyn . TypeError
      
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
    
    typee = Block . Compose . throwDyn . TypeError
    
instance S.Lit (Res k (Eval (Dyns k))) where
  unop_ op m = m <&> unop where
    unop ev en se = fromSelf (S.unop_ op (self (ev en se)))
    
  binop_ op m m' = liftA2 (binop op) m m' where
    binop op ev ev' en se =
      fromSelf (S.binop_ op
        (self (ev en se))
        (self (ev' en se)))
      
instance S.Local (Value (Dyns k a)) where
  local_ n = (Block . Compose
    . throwDyn
    . StaticError
    . ScopeError) (NotDefined n)
  
instance S.Local (Res k (Eval (Dyns k))) where
  local_ n = asks (elemIndex n)
    >>= maybe
      (tell [e] >> return (\ _ _ ->
        (Repr . Block . const . Compose
          . throwDyn) (StaticError e)))
      (\ i -> return (\ en _ -> en !! i))
    where 
      e = ScopeError (NotDefined n)
      
instance S.Self k => S.Self (Value (Dyns k a)) where
  self_ n = (Block . Compose
    . throwDyn
    . TypeError
    . NotComponent) (S.self_ n)
    
instance (S.Self k, Ord k) => S.Self (Res k (Eval (Dyns k))) where
  self_ n = pure (\ _ se -> self se `dynLookup` S.self_ n)

instance (S.Self k, Ord k) => S.Field (Res k (Eval (Dyns k))) where
  type Compound (Res k (Eval (Dyns k))) = Res k (Eval (Dyns k))
  m #. n = m <&> (\ ev en se ->
    self (ev en se) `dynLookup` S.self_ n)

    
instance (S.Self k, Ord k) => S.Tuple (Res k (Eval (Dyns k))) where
  type Tup (Res k (Eval (Dyns k))) = Tup k (Res k (Eval (Dyns k)))
      
  tup_ ts = dynCheckTup (foldMap (Comps . getTup) ts) <&>
    (\ kv en se ->
      (Repr . Block . const . fmap (\ ev -> ev en se) . Compose)
        (DynMap Nothing kv))
  
instance (S.Self k, Ord k) => S.Block (Res k (Eval (Dyns k))) where
  type Rec (Res k (Eval (Dyns k))) =
    Rec [P.Vis (Path k) (Path k)]
      (Patt (Decomps k) Bind, Res k (Eval (Dyns k)))
      
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
          k :: Repr (Dyns k) -> Dyns k (Repr (Dyns k))
          k se = Compose (DynMap Nothing kv) where
            kv = M.map (fmap (values se!!)) s
            
          values :: Repr (Dyns k) -> [Repr (Dyns k)]
          values se = vs
            where
              vs = foldMap
                (\ (p, ev) ->
                  match p (ev (en' ++ en) se))
                pas
             
              en' = localenv se vs
            
          localenv
            :: S.Self k
            => Repr (Dyns k) -> [Repr (Dyns k)] -> [Repr (Dyns k)]
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
      
instance Ord k => S.Extend (Res k (Eval (Dyns k))) where
  type Ext (Res k (Eval (Dyns k))) = Res k (Eval (Dyns k))
   
  (#) = liftA2 ext' where
    ext' evl evr en se = dynConcat (evl en se) (evr en se) 


data Dyn k a = DynMap (Maybe (DynError k)) (M.Map k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
type Dyns k = Compose (Dyn k) (Free (Dyn k))
  
unionWith
  :: Ord k
  => (a -> a -> a) -> Dyn k a -> Dyn k a -> Dyn k a
unionWith f (DynMap e kva) (DynMap Nothing kvb) = 
  DynMap e (M.unionWith f kva kvb)
unionWith _ _              d                    = d
  
throwDyn :: DynError k -> Dyn k a
throwDyn e = DynMap (Just e) M.empty
    
pruneDyn
  :: (a -> Maybe b)
  -> Free (Dyn k) a -> Maybe (Free (Dyn k) b)
pruneDyn f = go where
  go = iter pruneMap . fmap (fmap pure . f)
  
  pruneMap
    :: Dyn k (Maybe (Free (Dyn k) b))
    -> Maybe (Free (Dyn k) b)
  pruneMap (DynMap e kv) =
    maybeWrap (DynMap e (M.mapMaybe id kv))
    
  maybeWrap (DynMap Nothing kv) | M.null kv = Nothing
  maybeWrap d                               = Just (wrap d)

  
dynNumber _ = (const . Compose
  . throwDyn) (TypeError NoPrimitiveSelf)
dynText _ = (const . Compose
  . throwDyn) (TypeError NoPrimitiveSelf)
dynBool _ = (const . Compose
  . throwDyn) (TypeError NoPrimitiveSelf)
  
dynRepr
  :: Repr (Dyns k) -> Repr (Dyns k) -> Dyns k (Repr (Dyns k))
dynRepr (Repr v) = case v of
  Block k  -> k
  Number d -> dynNumber d
  Text t   -> dynText t
  Bool b   -> dynBool b
  
dynSelf :: Self (Dyns k) -> Dyns k (Repr (Dyns k))
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

  
displayDyn :: Dyns Ident a -> String
displayDyn (Compose (DynMap e kv)) = case (M.keys kv, e) of
  ([], Nothing) -> "<no components>"
  ([], Just e)  -> "<" ++ displayDynError e ++ ">"
  (ks, mb)      -> "<components: "
    ++ show (map (\ k -> showIdent k "") ks)
    ++ maybe "" (\ e -> " and " ++ displayDynError e) mb
    ++ ">"
  

dynLookup :: Ord k => Self (Dyns k) -> k -> Repr (Dyns k)
dynLookup v k = maybe 
  ((Repr . Block . const . Compose) (throwDyn e'))
  (\ m -> case runFree m of
    Pure r -> r
    Free dkv -> (Repr . Block . const) (Compose dkv))
  (M.lookup k kv)
  where
    Compose (DynMap e kv) = dynSelf v
    e' = fromMaybe (TypeError (NotComponent k)) e
      
      
dynConcat :: Ord k => Repr (Dyns k) -> Repr (Dyns k) -> Repr (Dyns k)
dynConcat r r' = (Repr . Block) (\ se -> 
  Compose (unionWith zip
    (getCompose (dynRepr r se))
    (getCompose (dynRepr r' se))))
  where
    zip m m' = free (zip' (runFree m) (runFree m'))
    
    zip' _          (Pure a')   = Pure a'
    zip' (Pure a)   (Free dkv') = (Pure
      . dynConcat a
      . Repr . Block
      . const) (Compose dkv')
    zip' (Free dkv) (Free dkv') = Free (unionWith zip dkv dkv')
  

type Match r = ReaderT r ((,) [r])

match
  :: (S.Self k, Ord k)
  => Patt (Dyns k) Bind
  -> Repr (Dyns k) -> [Repr (Dyns k)]
match (b :< Decomp ds) r = bind (r':xs) xs b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . matchDyn) ds <&> concat)
    r
  
  matchDyn
    :: (S.Self k, Ord k)
    => Dyns k (Patt (Dyns k) Bind)
    -> Match (Repr (Dyns k)) (Repr (Dyns k))
  matchDyn = matchMap
    . fmap (iter (fmap Just . matchMap))
    . getCompose
    . fmap liftPatt
    where
      liftPatt p = ReaderT (\ r -> (match p r, Nothing))
    
  matchMap
    :: (S.Self k, Ord k)
    => Dyn k
      (Match (Repr (Dyns k)) (Maybe (Repr (Dyns k))))
    -> Match (Repr (Dyns k)) (Repr (Dyns k))
  matchMap (DynMap eMatch kvMatch) = ReaderT (\ r ->
    let d = self r in 
    split d (DynMap eMatch kvMatch) <&> Repr . recomb d)
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split d (DynMap e kv) =
        traverseMaybeWithKey 
          (\ k m ->
            runReaderT m (d `dynLookup` k))
          kv <&> DynMap e
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb d dkv = Block (const (Compose dkv'))
        where
          Compose (DynMap ee kvv) = dynSelf d
          dkv' = unionWith (const id)
            (DynMap ee (withoutKeys kvv (M.keysSet kvMatch)))
            (fmap pure dkv)

  
dynCheckNode
  :: Applicative f
  => (k -> ([f a], f (Free (Dyn k) a)) -> f (Free (Dyn k) a))
  -> Node k (f a) -> ([f a], f (Free (Dyn k) a))
dynCheckNode check (Node m) = iterT freeDyn (fmap (fmap pure) m)
  where
    freeDyn = pure . fmap (wrap . DynMap Nothing)
        . M.traverseWithKey check
        
dynCheckStmts
  :: MonadWriter [StaticError k] f
  => (n -> DefnError k)
  -> n -> ([f b], f (Free (Dyn k) a))
  -> (f (Free (Dyn k) a))
dynCheckStmts throw n pp = case pp of
  ([], m) -> m
  (as, m) -> let e = DefnError (throw n) in
    tell [e] >> m >> sequenceA as >> (return . wrap
      . throwDyn) (StaticError e)
      
      
dynCheckDecomp
  :: MonadWriter [StaticError k] f
  => Decomps k (f a) -> f (Dyns k a)
dynCheckDecomp (Compose (Comps kv)) = Compose . DynMap Nothing <$>
  M.traverseWithKey
    (\ k -> check k . dynCheckNode check)
    kv
  where
    check = dynCheckStmts OlappedMatch
    
dynCheckPatt
  :: MonadWriter [StaticError k] f
  => Patt (Decomps k) a
  -> f (Patt (Dyns k) a)
dynCheckPatt (a :< Decomp cs) =
  (a :<) . Decomp <$>
    traverse (dynCheckDecomp . fmap dynCheckPatt) cs

dynCheckTup
  :: MonadWriter [StaticError k] f
  => Comps k (Node k (f a))
  -> f (M.Map k (Free (Dyn k) a))
dynCheckTup (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv
  where
    check = dynCheckStmts (OlappedSet . P.Pub)
      
      
dynCheckVis
  :: (S.Self k, Ord k, MonadWriter [StaticError k] f)
  => Vis k (Node k (Maybe a))
  -> f (Vis k (Free (Dyn k) a))
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
    
    pruneMap :: M.Map i (Free (Dyn k) (Maybe a))
      -> M.Map i (Free (Dyn k) a)
    pruneMap = M.mapMaybe (pruneDyn id)

      
    dynCheckPrivate
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map S.Ident (Node k a)
      -> f (M.Map S.Ident (Free (Dyn k) a))  
    dynCheckPrivate = M.traverseWithKey
      (\ n -> checkPriv n . dynCheckNode checkPub
        . fmap pure)
      
    dynCheckPublic
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map k (Node k a)
      -> f (M.Map k (Free (Dyn k) a))
    dynCheckPublic = M.traverseWithKey
      (\ k -> checkPub k . dynCheckNode checkPub
        . fmap pure)
      
    checkVis dupl = writer (f, es)
      where
        (Endo f, es) = M.foldMapWithKey
          (\ n _ -> let e = DefnError (OlappedVis n) in
            ((Endo . M.insert (S.self_ n)
              . wrap . throwDyn) (StaticError e), [e]))
          dupl
          
    checkPriv
      :: MonadWriter [StaticError k] f
      => S.Ident -> ([f a], f (Free (Dyn k) a))
      -> f (Free (Dyn k) a)
    checkPriv = dynCheckStmts (OlappedSet . P.Priv)
    
    checkPub
      :: MonadWriter [StaticError k] f
      => k -> ([f a], f (Free (Dyn k) a))
      -> f (Free (Dyn k) a)
    checkPub = dynCheckStmts (OlappedSet . P.Pub)
