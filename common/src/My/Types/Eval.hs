{-# LANGUAGE RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies, MultiParamTypeClasses, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable, ScopedTypeVariables #-}

module My.Types.Eval
  (Repr(..), Self, DynEval, eval, Dyn, displayValue)
  where
  
import qualified My.Types.Syntax.Class as S
import My.Syntax.Parser (showIdent)
import qualified My.Types.Syntax as P
import My.Types.Error
import My.Util ((<&>), traverseMaybeWithKey, restrictKeys)
import Control.Applicative (liftA2, Alternative(..))
import Control.Monad.Trans.Free
import Control.Monad.State
import Control.Monad.Reader hiding (local)
import Control.Comonad.Cofree
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Coerce
import Data.List (nub, elemIndex)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Data.Monoid (Endo(..))
import Data.Text (Text, unpack)
  
newtype Repr f = Repr (Repr f -> Value f (Repr f))

data Value f a =
    Block (f a)
  | Number Double
  | Text Text
  deriving Functor
  
type Self f = Value f (Repr f)

self :: Functor f => Repr f -> Self f
self (Repr k) = k (Repr k)


data DynMap k a = DynMap (Maybe (MyError k)) (M.Map k a)
  deriving (Functor, Foldable, Traversable)
  
unionWith
  :: Ord k
  => (a -> a -> a) -> DynMap k a -> DynMap k a -> DynMap k a
unionWith f (DynMap e ma) (DynMap Nothing mb) = 
  DynMap e (M.unionWith f ma mb)
unionWith _ _             d                   = d
  
newtype Dyn k a = Dyn (DynMap k (Free (DynMap k) a))
  deriving (Functor, Foldable, Traversable)
  
unionDyn
  :: Ord k
  => (a       -> Dyn k a -> a)
  -> (Dyn k a -> a       -> a)
  -> (a       -> a       -> a)
  -> Dyn k a -> Dyn k a -> Dyn k a
unionDyn lp rp bp (Dyn dma) (Dyn dmb) =
  Dyn (unionWith zipFD dma dmb)
  where
    zipFD fa fb = free (zipFF (runFree fa) (runFree fb))
    
    zipFF (Pure a  ) (Free dmb) = Pure (lp a         (Dyn dmb))
    zipFF (Free dma) (Pure b  ) = Pure (rp (Dyn dma) b        )
    zipFF (Pure a  ) (Pure b  ) = Pure (bp a         b        )
    zipFF (Free dma) (Free dmb) = Free (unionWith zipFD dma dmb)
    
pruneDyn
  :: (a -> Maybe b)
  -> Free (DynMap k) a -> Maybe (Free (DynMap k) b)
pruneDyn f = go where
  go = iter pruneMap . fmap (fmap pure . f)
  
  pruneMap
    :: DynMap k (Maybe (Free (DynMap k) b))
    -> Maybe (Free (DynMap k) b)
  pruneMap (DynMap e m) =
    maybeWrap (DynMap e (M.mapMaybe id m))
    
  maybeWrap (DynMap Nothing m) | M.null m = Nothing
  maybeWrap d                             = Just (wrap d)
  
  
dynNumber d =
  DynMap (Just (PrimError NoPrimitiveSelf)) M.empty
  
dynText t =
  DynMap (Just (PrimError NoPrimitiveSelf)) M.empty
  
runDyn :: Value (Dyn k) a -> DynMap k (Free (DynMap k) a)
runDyn (Block (Dyn dm))   = dm
runDyn (Number d)         = dynNumber d
runDyn (Text t)           = dynText t

displayValue :: Value (Dyn S.Ident) a -> String
displayValue (Number d) = show d
displayValue (Text t)   = unpack t
displayValue (Block (Dyn (DynMap e m))) = case (M.keys m, e) of
  ([], Nothing) -> "<no components>"
  ([], Just e)  -> "<" ++ displayError e ++ ">"
  (ks, mb) -> "<components: "
    ++ show (map (\ k -> showIdent k "") ks)
    ++ maybe "" (\ e -> " and " ++ displayError e) mb
    ++ ">"
  

lookupDyn :: Ord k => Self (Dyn k) -> k -> Repr (Dyn k)
lookupDyn v k =
  maybe 
    ((Repr . const . Block . Dyn) (DynMap e' M.empty))
    (\ f -> case runFree f of
      Pure r -> r
      Free dm -> (Repr . const . Block) (Dyn dm))
    (M.lookup k m)
  where
    DynMap e m = runDyn v
    e' = e <|> Just (KeyError (NotComponent k))
      
concatDyn :: Ord k => Self (Dyn k) -> Self (Dyn k) -> Self (Dyn k)
concatDyn v1 v2 = Block (unionDyn
  (\ (Repr k) db -> Repr (\ se -> concatDyn (k se) (Block db)))
  (\ _         b  -> b)
  (\ _         b  -> b)
  (Dyn (runDyn v1))
  (Dyn (runDyn v2)))
  
  
type DynEval k =
  [S.Ident] -> [Repr (Dyn k)] -> Repr (Dyn k) -> Repr (Dyn k)
  
eval :: DynEval k -> Self (Dyn k)
eval res = (self . res [] [] . Repr . const . Block . Dyn)
  (DynMap (Just (PrimError NoGlobalSelf)) M.empty)
  
instance S.Local (DynEval k) where
  local_ i ns en _ = maybe
    ((Repr . const . Block . Dyn)
      (DynMap ((Just . ScopeError) (NotDefined i)) M.empty))
    (en !!)
    (elemIndex i ns)
    
instance (S.Self k, Ord k) => S.Self (DynEval k) where
  self_ i _ _ se = self se `lookupDyn` S.self_ i
  
instance (S.Self k, Ord k) => S.Field (DynEval k) where
  type Compound (DynEval k) = DynEval k
  (res #. i) n en se = self (res n en se) `lookupDyn` S.self_ i
  
type instance S.Member (DynEval k) = DynEval k
  
instance (S.Self k, Ord k) => S.Tuple (DynEval k) where
  type Tup (DynEval k) = Tup k (DynEval k)
      
  tup_ ts ns en se =
    (Repr . const . Block
      . fmap (\ res -> res ns en se)
      . Dyn)
      (DynMap Nothing m)
    where
      m = dynCheckTup (foldMap getTup ts)
  
instance (S.Self k, Ord k) => S.Block (DynEval k) where
  type Rec (DynEval k) =
    Rec [P.Vis Path Path] (Patt (Dyn k) Bind, DynEval k)
      
  block_ rs ns en _ = Repr k
    where
      (v, pas, ns') = buildVis rs
      Vis{local=l,public=s} = dynCheckVis v
      (dupl, undupl) = M.partitionWithKey
        (\ i _ -> S.self_ i `M.member` s)
        (M.mapMaybe (pruneDyn id) l)
      s' = appEndo (M.foldMapWithKey
        (\ i _ ->
          (Endo . M.insert (S.self_ i) . wrap)
            (DynMap
              ((Just . DefnError) (OlappedVis i))
              M.empty))
        dupl) (M.mapMaybe (pruneDyn id) s)
      
      k :: Repr (Dyn k) -> Self (Dyn k)
      k se = (Block . Dyn) (DynMap Nothing m) where
        m = M.map (fmap (vs!!)) s'
        vs = values se
      
      localenv
        :: S.Self k
        => Repr (Dyn k) -> [Repr (Dyn k)] -> [Repr (Dyn k)]
      localenv se vs = en' where
        en' = map
          (\ i ->
            M.findWithDefault (self se `lookupDyn` S.self_ i) i l')
          ns'
        l' = M.mapWithKey
          (\ i f -> case runFree (fmap (vs !!) f) of
            Pure r -> r
            Free dm -> maybe 
              ((Repr . const . Block) (Dyn dm))
              (\ n ->
                (Repr . const
                  . concatDyn (self (en !! n))
                  . Block) (Dyn dm))
              (elemIndex i ns))
          undupl
      
      values :: Repr (Dyn k) -> [Repr (Dyn k)]
      values se = vs
        where
          vs = foldMap
            (\ (p, res) ->
              match p (res (ns' ++ ns) (en' ++ en) se))
            pas 
         
          en' = localenv se vs
      
instance Ord k => S.Extend (DynEval k) where
  type Ext (DynEval k) = DynEval k
    
  (resl # resr) ns en se =
    concatBlock (resl ns en se) (resr ns en se) where 
    concatBlock (Repr kl) (Repr kr) =
      Repr (liftA2 concatDyn kl kr)

      
-- | Pattern
type Patt f = Cofree (Decomp f)
newtype Decomp f a = Decomp { getDecomp :: [f a] }
  deriving (Functor, Foldable, Traversable)
  
letpath :: a -> Patt f a
letpath a = a :< Decomp []
  
instance S.Self a => S.Self (Patt f (Maybe a)) where
  self_ i = letpath (Just (S.self_ i))
  
instance S.Local a => S.Local (Patt f (Maybe a)) where
  local_ i = letpath (Just (S.local_ i))
  
instance S.Field a => S.Field (Patt f (Maybe a)) where
  type Compound (Patt f (Maybe a)) = S.Compound a
  p #. i = letpath (Just (p S.#. i))
  
type instance S.Member (Patt f a) = Patt f a

instance (S.Self k, Ord k, S.VarPath a)
  => S.Tuple (Patt (Dyn k) (Maybe a)) where
  type Tup (Patt (Dyn k) (Maybe a)) =
    Tup k (Patt (Dyn k) (Maybe a))
    
  tup_ ts = Nothing :< S.tup_ ts
  
type instance S.Member (Decomp f a) = a
  
instance (S.Self k, Ord k, S.VarPath a)
  => S.Tuple (Decomp (Dyn k) a) where
  type Tup (Decomp (Dyn k) a) = Tup k a
  tup_ ts = Decomp  [d] where
    d = (Dyn . DynMap Nothing
      . dynCheckDecomp) (foldMap getTup ts)
  
instance S.Extend (Patt (Dyn k) a) where
  type Ext (Patt (Dyn k) a) = Decomp (Dyn k) (Patt (Dyn k) a)
  (a :< Decomp ns) # Decomp ns' = a :< Decomp (ns' ++ ns)
    
dynCheckDecomp :: Comps k a -> M.Map k (Free (DynMap k) a)
dynCheckDecomp (Comps m) = M.mapWithKey
  (\ k -> check k . dynCheckNode check)
  m
  where
    check = dynCheckStmts (const . DefnError . OlappedMatch)
  
-- | A leaf pattern that can bind the matched value or skip
data Bind = Bind | Skip

bind :: a -> a -> Bind -> a
bind a _ Bind = a
bind _ a Skip = a

type Match r = ReaderT r ((,) [r])

match
  :: (S.Self k, Ord k)
  => Patt (Dyn k) Bind -> Repr (Dyn k) -> [Repr (Dyn k)]
match (b :< Decomp ds) r = bind xs (r':xs) b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . matchDyn) ds <&> concat)
    r
  
  matchDyn
    :: (S.Self k, Ord k)
    => Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  matchDyn d =
    matchMap (fmap (iter matchMap') dm)
    where
      Dyn dm = fmap
        (\ p ->
          ReaderT (\ r -> (match p r, Nothing)))
        d
      matchMap' = fmap Just . matchMap
    
  matchMap
    :: (S.Self k, Ord k)
    => DynMap k
      (Match (Repr (Dyn k)) (Maybe (Repr (Dyn k))))
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  matchMap (DynMap e m) = ReaderT (\ r -> let d = self r in 
    split d (DynMap e m) <&> Repr . const . recomb d)
    where
      split d (DynMap e m) =
        traverseMaybeWithKey 
          (\ k m ->
            runReaderT m (d `lookupDyn` k))
          m <&> Block . Dyn . DynMap e . fmap pure
        
      recomb d d' =
        concatDyn
          ((Block . Dyn) (DynMap
            ee
            (restrictKeys mm (M.keysSet m))))
          d'
        where
          DynMap ee mm = runDyn d
      

  
-- | Thread a writer through levels of a tree of paths
newtype Node k w a = Node { getNode ::
  FreeT (M.Map k) ((,) w) a }
  deriving (Functor, Foldable, Traversable, Applicative, Monad)
  
instance Bifunctor (Node k) where
  bimap f g (Node (FreeT p)) =
    (Node . FreeT)
      (bimap f (bimap g (getNode . bimap f g . Node)) p)
    
instance Bifoldable (Node k) where
  bifoldMap f g (Node (FreeT p)) =
    bifoldMap f (bifoldMap g (bifoldMap f g . Node)) p
    
instance Bitraversable (Node k) where
  bitraverse f g (Node (FreeT p)) =
    Node . FreeT <$>
      (bitraverse f . bitraverse g) (fmap getNode
        . bitraverse f g . Node) p
  
instance (Monoid w, S.Self k)
  => MonadFree ((,) S.Ident) (Node k w) where
  wrap (i, Node m) = Node (wrap (M.singleton (S.self_ i) m))

instance Ord k => Monoid (Node k [a] a) where
  mempty = Node (liftF M.empty)
  
  Node m1 `mappend` Node m2 = Node (mappend' m1 m2) where
    mappend' (FreeT (as1, Pure a1)) (FreeT (as2, ff2    )) =
      FreeT ([a1] ++ as1 ++ as2, ff2    )
    mappend' (FreeT (as1, ff1    )) (FreeT (as2, Pure a2)) =
      FreeT (as1 ++ [a2] ++ as2, ff1    )
    mappend' (FreeT (as1, Free m1)) (FreeT (as2, Free m2)) =
      FreeT (as1 ++ as2        , Free m')
      where
        m' = M.unionWith mappend' m1 m2
  
dynCheckNode
  :: forall k a . (k -> ([a], Free (DynMap k) a) -> Free (DynMap k) a)
  -> Node k [a] a -> ([a], Free (DynMap k) a)
dynCheckNode check (Node m) = iterT freeDyn (fmap pure m)
  where
    freeDyn
      :: M.Map k ([a], Free (DynMap k) a)
      -> ([a], Free (DynMap k) a)
    freeDyn = pure . wrap . DynMap Nothing . M.mapWithKey check
        
dynCheckStmts
  :: (i -> [a] -> MyError k)
  -> i -> ([a], Free (DynMap k) a) -> Free (DynMap k) a
dynCheckStmts throw i p = case p of
  ([], m) -> m
  (as, _) -> wrap (DynMap (Just (throw i as)) M.empty)
  
-- | Tree of components
newtype Comps k a = Comps (M.Map k (Node k [a] a))

instance Functor (Comps k) where
  fmap f (Comps m) = Comps (fmap (bimap (fmap f) f) m)
  
instance Foldable (Comps k) where
  foldMap f (Comps m) = foldMap (bifoldMap (foldMap f) f) m
  
instance Traversable (Comps k) where
  traverse f (Comps m) =
    fmap Comps (traverse (bitraverse (traverse f) f) m)
  
instance Ord k => Monoid (Comps k a) where
  mempty = Comps M.empty
  Comps m1 `mappend` Comps m2 = Comps (M.unionWith mappend m1 m2)
  
dynCheckTup :: Comps k a -> M.Map k (Free (DynMap k) a)
dynCheckTup (Comps m) = M.mapWithKey
  (\ k -> check k . dynCheckNode check)
  m
  where
    check = dynCheckStmts (const . DefnError
      . OlappedSet . P.Pub)
  
-- | Generic constructor for a tuple
newtype Tup k a = Tup { getTup :: Comps k a }
  
instance (S.Self k, S.Self a) => S.Self (Tup k a) where
  self_ i = pun (S.self_ i)
instance (S.Self k, S.Local a) => S.Local (Tup k a) where
  local_ i = pun (S.local_ i)

instance (S.Self k, S.Field a) => S.Field (Tup k a) where
  type Compound (Tup k a) = Pun Path (S.Compound a)
  p #. i = pun (p S.#. i)

instance S.Self k => S.Assoc (Tup k a) where
  type Label (Tup k a) = Path
  type Value (Tup k a) = a
  Path i f #: a =
    (Tup . Comps . M.singleton (S.self_ i) . f) (pure a)
 
 
-- | Recursive block with destructing pattern assignments. 
newtype Rec w a = Rec (w, Maybe a)

decl :: s -> Rec [s] a
decl s = Rec ([s], Nothing)
  
  
instance S.Self s => S.Self (Rec [s] a) where
  self_ i = decl (S.self_ i)

instance S.Field s => S.Field (Rec [s] a) where
  type Compound (Rec [s] a) = S.Compound s
  p #. i = decl (p S.#. i)

instance (Traversable f, S.Patt (f (Maybe s)))
  => S.Let (Rec [s] (f Bind, a)) where
  type Lhs (Rec [s] (f Bind, a)) = f (Maybe s)
  type Rhs (Rec [s] (f Bind, a)) = a
  p #= a = Rec (traverse 
    (maybe (pure Skip) (\ s -> ([s], Bind)))
    p <&> (\ p' -> Just (p', a)))
  
  
-- | Builder for a path
data Path =
  Path
    S.Ident
    (forall m a. MonadFree ((,) S.Ident) m => m a -> m a)

instance S.Self Path where self_ i = Path i id
instance S.Local Path where local_ i = Path i id
  
instance S.Field Path where
  type Compound Path = Path
  Path n f #. i = Path n (f . wrap . (,) i)
      
-- | A 'punned' assignment statement generates an assignment path corresponding to a
-- syntactic value definition. E.g. the statement 'a.b.c' assigns the value 'a.b.c' to the
-- path '.a.b.c'.
data Pun p a = Pun p a

pun :: S.Assoc s => Pun (S.Label s) (S.Value s) -> s
pun (Pun p a) = p S.#: a

instance (S.Self p, S.Self a) => S.Self (Pun p a) where self_ i = Pun (S.self_ i) (S.self_ i)
instance (S.Self p, S.Local a) => S.Local (Pun p a) where
  local_ i = Pun (S.self_ i) (S.local_ i)

instance (S.Field p, S.Field a) => S.Field (Pun p a) where
  type Compound (Pun p a) = Pun (S.Compound p) (S.Compound a)
  Pun p a #. i = Pun (p S.#. i) (a S.#. i)
  
  
-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data Vis k a = Vis { local :: M.Map S.Ident a, public :: M.Map k a }
--  deriving Functor
  
introVis
  :: S.Self k => a -> P.Vis Path Path -> Vis k (Node k [a] a)
introVis a (P.Pub (Path i f)) =
  Vis{local=M.empty,public=(M.singleton (S.self_ i) (f (pure a)))}
introVis a (P.Priv (Path i f)) =
  Vis{local=(M.singleton i (f (pure a))),public=M.empty}

instance (Ord k, Monoid a) => Monoid (Vis k a) where
  mempty = Vis{local=M.empty,public=M.empty}
  Vis{local=l1,public=s1} `mappend` Vis{local=l2,public=s2} =
    Vis{local=(M.unionWith mappend l1 l2),public=(M.unionWith mappend s1 s2)}

buildVis
  :: forall a k . (S.Self k, Ord k)
  => [Rec [P.Vis Path Path] a]
  -> (Vis k (Node k [Maybe Int] (Maybe Int)), [a], [S.Ident])
buildVis rs = (r, pas, nub (ns)) where
    
  pas = mapMaybe (\ (Rec (_, pa)) -> pa) rs
  (r, ns) = foldMap (\ (mb, s) -> (introVis mb s, pure (name s))) (enumJust (coerce rs :: [([P.Vis Path Path], Maybe a)]))
  
  name :: P.Vis Path Path -> S.Ident
  name (P.Pub (Path i _)) = i
  name (P.Priv (Path i _)) = i
  
  enumJust :: forall a b . [([a], Maybe b)] -> [(Maybe Int, a)]
  enumJust cs = concat (evalState (traverse enumPair cs) 0) where
    
    enumPair (xs, Just _) = 
      traverse (\ a -> state (\ i -> ((Just i, a), i+1))) xs
    enumPair (xs, Nothing) = pure (map ((,) Nothing) xs)

    
dynCheckVis
  :: Vis k (Node k [a] a)
  -> Vis k (Free (DynMap k) a)
dynCheckVis (Vis{local=l,public=s}) = Vis{local=l',public=s'}
  where
    l' = M.mapWithKey
      (\ i -> checkPriv i . dynCheckNode checkPub)
      l
    s' = M.mapWithKey
      (\ k -> checkPub k . dynCheckNode checkPub)
      s
    
    checkPub = dynCheckStmts (const . DefnError
      . OlappedSet . P.Pub)
    checkPriv = dynCheckStmts (const . DefnError
      . OlappedSet . P.Priv)
    