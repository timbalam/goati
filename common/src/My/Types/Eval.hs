{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

module My.Types.Eval
  (Repr(..), Self, Res, Eval, eval, Dyn, displayValue)
  where
  
import My.Types.Error
import My.Syntax.Parser (showIdent)
import qualified My.Types.Syntax.Class as S
import qualified My.Types.Syntax as P
import My.Types.Paths.Rec
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
import Data.Coerce
import Data.List (nub, elemIndex)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Monoid (Endo(..))
import Data.String (IsString(..))
import Data.Text (Text, unpack)
import Data.Tuple (swap)
  
newtype Repr f = Repr (Repr f -> Value f (Repr f))

instance Eq (Repr f)
instance Show (Repr f)

data Value f a =
    Block (f a)
  | Number Double
  | Text Text
  | Bool Bool
  deriving (Eq, Show, Functor)
  
type Self f = Value f (Repr f)

self :: Repr f -> Self f
self (Repr k) = k (Repr k)

fromSelf :: Self f -> Repr f
fromSelf v = Repr (const v)


data DynMap k a = DynMap (Maybe (DynError k)) (M.Map k a)
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
unionWith
  :: Ord k
  => (a -> a -> a) -> DynMap k a -> DynMap k a -> DynMap k a
unionWith f (DynMap e kva) (DynMap Nothing kvb) = 
  DynMap e (M.unionWith f kva kvb)
unionWith _ _              d                    = d
  
throwDyn :: DynError k -> DynMap k a
throwDyn e = DynMap (Just e) M.empty
  
newtype Dyn k a = Dyn (DynMap k (Free (DynMap k) a))
  deriving (Eq, Show, Functor, Foldable, Traversable)
  
unionDyn
  :: Ord k
  => (a       -> Dyn k a -> a)
  -> (Dyn k a -> a       -> a)
  -> (a       -> a       -> a)
  -> Dyn k a -> Dyn k a -> Dyn k a
unionDyn lp rp bp (Dyn dkva) (Dyn dkvb) =
  Dyn (unionWith zipFD dkva dkvb)
  where
    zipFD fa fb = free (zipFF (runFree fa) (runFree fb))
    
    zipFF (Pure a)    (Free dkvb) = Pure (lp a (Dyn dkvb))
    zipFF (Free dkva) (Pure b)    = Pure (rp (Dyn dkva) b)
    zipFF (Pure a)    (Pure b)    = Pure (bp a b)
    zipFF (Free dkva) (Free dkvb) =
      Free (unionWith zipFD dkva dkvb)
    
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

  
dynNumber _ = throwDyn (TypeError NoPrimitiveSelf)
dynText _ = throwDyn (TypeError NoPrimitiveSelf)
dynBool _ = throwDyn (TypeError NoPrimitiveSelf)
  
runDyn :: Value (Dyn k) a -> DynMap k (Free (DynMap k) a)
runDyn (Block (Dyn dkv)) = dkv
runDyn (Number d)        = dynNumber d
runDyn (Text t)          = dynText t
runDyn (Bool b)          = dynBool b

  
displayValue :: Value (Dyn S.Ident) a -> String
displayValue = display' where
  display' (Number d) = show d
  display' (Text t)   = unpack t
  display' (Bool b)   =
    "<bool: " ++ if b then "true" else "false" ++ ">"
  display' (Block (Dyn d)) = displayDyn d

  displayDyn (DynMap e kv) = case (M.keys kv, e) of
    ([], Nothing) -> "<no components>"
    ([], Just e)  -> "<" ++ displayDynError e ++ ">"
    (ks, mb) -> "<components: "
      ++ show (map (\ k -> showIdent k "") ks)
      ++ maybe "" (\ e -> " and " ++ displayDynError e) mb
      ++ ">"
  

lookupDyn :: Ord k => Self (Dyn k) -> k -> Repr (Dyn k)
lookupDyn v k =
  maybe 
    ((fromSelf . Block . Dyn) (throwDyn e'))
    (\ f -> case runFree f of
      Pure r -> r
      Free dkv -> (fromSelf . Block) (Dyn dkv))
    (M.lookup k kv)
  where
    DynMap e kv = runDyn v
    e' = fromMaybe (TypeError (NotComponent k)) e
      
concatDyn :: Ord k => Self (Dyn k) -> Self (Dyn k) -> Self (Dyn k)
concatDyn v1 v2 = Block (unionDyn
  (\ (Repr k) db -> Repr (\ se -> concatDyn (k se) (Block db)))
  (\ _        b  -> b)
  (\ _        b  -> b)
  (Dyn (runDyn v1))
  (Dyn (runDyn v2)))
  
  
type Res k = ReaderT [S.Ident] (Writer [StaticError k])
type Eval f = [Repr f] -> Repr f -> Repr f
  
eval :: Res k (Eval (Dyn k)) -> ([StaticError k], Self (Dyn k))
eval m = (swap . runWriter) (runReaderT m []) <&> (\ ev ->
  self (ev [] r0))
  where
    r0 = (fromSelf . Block . Dyn) (DynMap Nothing M.empty)
      
nume = error "Num (Self f)"

instance Num (Self f) where
  fromInteger = Number . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
instance Num (Res k (Eval f)) where
  fromInteger i = pure (\ _ _ -> fromSelf (fromInteger i))
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Fractional (Self f)"

instance Fractional (Self f) where
  fromRational = Number . fromRational
  (/) = frace
  
instance Fractional (Res k (Eval f)) where
  fromRational r = pure (\ _ _ -> fromSelf (fromRational r))
  (/) = frace
  
instance IsString (Self f) where
  fromString = Text . fromString
  
instance IsString (Res k (Eval f)) where
  fromString s = pure (\ _ _ -> fromSelf (fromString s))
      
instance S.Lit (Self (Dyn k)) where
  unop_ = unop where 
    unop S.Not (Bool b)   = Bool (not b)
    unop S.Not _          = typee NotBool
    unop S.Neg (Number d) = Number (negate d)
    unop S.Neg _          = typee NotNumber
    
    typee = Block . Dyn . throwDyn . TypeError
      
  binop_ = binop where
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
    
    typee = Block . Dyn . throwDyn . TypeError
    
instance S.Lit (Res k (Eval (Dyn k))) where
  unop_ op m = m <&> unop where
    unop ev en se = (fromSelf . S.unop_ op . self) (ev en se)
    
  binop_ op m m' = liftA2 (binop op) m m' where
    binop op ev ev' en se =
      fromSelf (S.binop_ op (self (ev en se)) (self (ev' en se)))
      
instance S.Local (Self (Dyn k)) where
  local_ n = (Block . Dyn . throwDyn
    . StaticError
    . ScopeError) (NotDefined n)
  
instance S.Local (Res k (Eval (Dyn k))) where
  local_ n = asks (elemIndex n) >>= maybe
    (tell [e] >> return (\ _ _ -> (Repr . const
      . Block . Dyn . throwDyn) (StaticError e)))
    (\ i -> return (\ en _ -> en !! i))
    where 
      e = ScopeError (NotDefined n)
      
instance S.Self k => S.Self (Self (Dyn k)) where
  self_ n = (Block . Dyn . throwDyn
    . TypeError . NotComponent) (S.self_ n)
    
instance (S.Self k, Ord k) => S.Self (Res k (Eval (Dyn k))) where
  self_ n = pure (\ _ se -> self se `lookupDyn` S.self_ n)

instance (S.Self k, Ord k) => S.Field (Res k (Eval (Dyn k))) where
  type Compound (Res k (Eval (Dyn k))) = Res k (Eval (Dyn k))
  m #. n = m <&> (\ ev en se ->
    self (ev en se) `lookupDyn` S.self_ n)
  
--type instance S.Member (Res k (Eval (Dyn k))) = Res k (Eval (Dyn k))
  
instance (S.Self k, Ord k) => S.Tuple (Res k (Eval (Dyn k))) where
  type Tup (Res k (Eval (Dyn k))) = Tup k (Res k (Eval (Dyn k)))
      
  tup_ ts = dynCheckTup (foldMap getTup ts) <&> (\ kv en se ->
    (Repr . const . Block
      . fmap (\ ev -> ev en se)
      . Dyn)
      (DynMap Nothing kv))
  
instance (S.Self k, Ord k) => S.Block (Res k (Eval (Dyn k))) where
  type Rec (Res k (Eval (Dyn k))) =
    Rec [P.Vis Path Path]
      (Patt (Comps k) Bind, Res k (Eval (Dyn k)))
      
  block_ rs = liftA3 evalBlock
    (dynCheckVis v)
    (local (ns'++) (traverse
      (bitraverse dynCheckPatt id)
      pas))
    ask
    where
      (v, pas, ns') = buildVis rs
      
      evalBlock (Vis{private=l,public=s}) pas ns en _ = Repr k
        where
          k :: Repr (Dyn k) -> Self (Dyn k)
          k se = (Block . Dyn) (DynMap Nothing kv) where
            kv = M.map (fmap (vs!!)) s
            vs = values se
            
          localenv
            :: S.Self k
            => Repr (Dyn k) -> [Repr (Dyn k)] -> [Repr (Dyn k)]
          localenv se vs = en' where
            en' = map
              (\ n -> M.findWithDefault
                (self se `lookupDyn` S.self_ n)
                n
                lext)
              ns'
              
            -- extend inherited local bindings
            lext = M.mapWithKey
              (\ n m -> case runFree (fmap (vs!!) m) of
                Pure r -> r
                Free dkv -> maybe 
                  ((Repr . const . Block) (Dyn dkv))
                  (\ i ->
                    (Repr . const
                      . concatDyn (self (en !! i))
                      . Block) (Dyn dkv))
                  (elemIndex n ns))
              l
          
          values :: Repr (Dyn k) -> [Repr (Dyn k)]
          values se = vs
            where
              vs = foldMap
                (\ (p, ev) ->
                  match p (ev (en' ++ en) se))
                pas
             
              en' = localenv se vs
      
instance Ord k => S.Extend (Res k (Eval (Dyn k))) where
  type Ext (Res k (Eval (Dyn k))) = Res k (Eval (Dyn k))
   
  (#) = liftA2 ext' where
    ext' evl evr en se = concatBlock (evl en se) (evr en se) 
    
    concatBlock (Repr kl) (Repr kr) =
      Repr (liftA2 concatDyn kl kr)

    
dynCheckDecomp
  :: MonadWriter [StaticError k] f
  => Comps k (f a) -> f (Dyn k a)
dynCheckDecomp (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv <&> Dyn . DynMap Nothing
  where
    check = dynCheckStmts OlappedMatch
    
dynCheckPatt
  :: MonadWriter [StaticError k] f
  => Patt (Comps k) a -> f (Patt (Dyn k) a)
dynCheckPatt (a :< Decomp cs) =
  (a :<) . Decomp <$>
    traverse (dynCheckDecomp . fmap dynCheckPatt) cs
  

type Match r = ReaderT r ((,) [r])

match
  :: (S.Self k, Ord k)
  => Patt (Dyn k) Bind -> Repr (Dyn k) -> [Repr (Dyn k)]
match (b :< Decomp ds) r = bind (r':xs) xs b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . matchDyn) ds <&> concat)
    r
  
  matchDyn
    :: (S.Self k, Ord k)
    => Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  matchDyn (Dyn dm) =
    matchMap (fmap (iter (fmap Just . matchMap) . fmap liftPatt) dm)
    where
      liftPatt p = ReaderT (\ r -> (match p r, Nothing))
    
  matchMap
    :: (S.Self k, Ord k)
    => DynMap k
      (Match (Repr (Dyn k)) (Maybe (Repr (Dyn k))))
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  matchMap (DynMap eMatch kvMatch) = ReaderT (\ r -> let d = self r in 
    split d (DynMap eMatch kvMatch) <&> fromSelf . recomb d)
    where
      -- for keys in matching pattern, split the corresponding
      -- key from the input
      split d (DynMap e kv) =
        traverseMaybeWithKey 
          (\ k m ->
            runReaderT m (d `lookupDyn` k))
          kv <&> DynMap e
      
      -- for keys in matching pattern, delete and 
      -- replace any unmatched parts
      recomb d dm = Block (Dyn dm')
        where
          DynMap ee kvv = runDyn d
          dm' = unionWith (const id)
            (DynMap ee (withoutKeys kvv (M.keysSet kvMatch)))
            (fmap pure dm)
      

  
dynCheckNode
  :: Applicative f
  => (k -> ([f a], f (Free (DynMap k) a)) -> f (Free (DynMap k) a))
  -> Node k [f a] (f a) -> ([f a], f (Free (DynMap k) a))
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
      . throwDyn) (StaticError e)

dynCheckTup
  :: MonadWriter [StaticError k] f
  => Comps k (f a)
  -> f (M.Map k (Free (DynMap k) a))
dynCheckTup (Comps kv) = M.traverseWithKey
  (\ k -> check k . dynCheckNode check)
  kv
  where
    check = dynCheckStmts (OlappedSet . P.Pub)
      
  
  

    
dynCheckVis
  :: (S.Self k, Ord k, MonadWriter [StaticError k] f)
  => Vis k (Node k [Maybe a] (Maybe a))
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
      => M.Map S.Ident (Node k [a] a)
      -> f (M.Map S.Ident (Free (DynMap k) a))  
    dynCheckPrivate = M.traverseWithKey
      (\ n -> checkPriv n . dynCheckNode checkPub
        . bimap (fmap pure) pure)
      
    dynCheckPublic
      :: (Ord k, MonadWriter [StaticError k] f)
      => M.Map k (Node k [a] a)
      -> f (M.Map k (Free (DynMap k) a))
    dynCheckPublic = M.traverseWithKey
      (\ k -> checkPub k . dynCheckNode checkPub
        . bimap (fmap pure) pure)
      
    checkVis dupl = writer (f, es)
      where
        (Endo f, es) = M.foldMapWithKey
          (\ n _ -> let e = DefnError (OlappedVis n) in
            ((Endo . M.insert (S.self_ n)
              . wrap . throwDyn) (StaticError e), [e]))
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
    
      
    