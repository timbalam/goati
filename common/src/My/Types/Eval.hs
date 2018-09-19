module My.Types.Eval
  ( 
  )
  where
  
import qualified Data.Map as M
import qualified My.Types.Syntax.Class as S
import My.Types.Error
  
newtype Repr f = Block (f (Repr f -> Repr f))
type Self f = f (Repr f)


newtype DynMap k a =
  DynMap { getDynMap :: Either [MyError] (M.Map (Tag k) a) }
  deriving Functor
  
newtype Dyn k a =
  Dyn { getDyn :: DynMap k (Free (DynMap k) a) }
  deriving Functor
  
newtype Dyn' k a =
  Dyn' { getDyn' :: Either [MyError]
    (M.Map (Tag k) (FreeT (M.Map (Tag k)) (Either [MyError]) a)) }
  deriving Functor
  
zipDyn
  :: (a -> DynMap k b -> c)
  -> (DynMap k a -> b -> c)
  -> (a -> b -> c)
  -> Dyn k a -> Dyn k b -> Dyn k c
zipDyn lp rp bp (Dyn dma) (Dyn dmb) = zipD dma dmb where
  zipD (DynMap ea) (DynMap eb) =
    DynMap (liftA2 (M.unionWith zipFD) ea eb)

  zipFD (Pure a)   (Pure b)   = Pure (bp a b)
  zipFD (Pure a)   (Free dmb) = Pure (lp a mb)
  zipFD (Free dma) (Pure b)   = Pure (rp ma b)
  zipFD (Free dma) (Free dmb) = Free (zipD dma dmb)

graftDyn
  :: Dyn k a
  -> (a -> Free (DynMap k) b)
  -> Dyn k b
graftDyn (Dyn m) f = Dyn (fmap (>>= f) m)

self :: Functor f => Repr f -> Self f
self (Block d) = fmap (`id` Block d) d

dynGet :: Self (Dyn k) -> Key k -> Repr (Dyn k)
dynGet (Dyn (DynMap e)) k =
  either
    (Block . DynMap . Left)
    (\ f -> case  f of
      Pure r -> r
      Free d -> Block (fmap const d)
    (e >>= maybe
      (Left [KeyError (NotComponent k)])
      Right
      . M.lookup k)
  
  
type Res a = [Ident] -> Either [MyError] a
  
instance S.Local (Res ([a] -> a)) where
  local_ i = maybe
    (Left [ScopeError (NotDefined i)])
    (Right (\ n en -> en !! n))
    . elemIndex i
    
instance S.Self (Repr (Dyn k) -> Repr (Dyn k)) where
    self_ i r = self r `dynGet` Key i
  
instance S.Tuple (Res ([Repr (Dyn k)]
  -> Repr (Dyn k) -> Repr (Dyn k))) where
  type Tup (Res ([Repr (Dyn k)]
    -> Repr (Dyn k) -> Repr (Dyn k))) =
    Tup k (Res ([Repr (Dyn k)]
      -> Repr (Dyn k) -> Repr (Dyn k)))
      
  tup_ ts ns = pure (\ en se -> let
    Dyn dm = dynCheck (foldMap getTup ts)
    f res = either (Free . DynMap . Left) Pure
      (res ns <&> (\ k -> k en se))
    in Block (Dyn (fmap (>>= f) dm)))
  
instance S.Rec (Res ([Repr (Dyn k)]
  -> Repr (Dyn k) -> Repr (Dyn k))) where
  type Rec (Res ([Repr (Dyn k)]
    -> Repr (Dyn k) -> Repr (Dyn k))) =
    Rec [P.Vis Path Path] (Patt Bind, Res ([Repr (Dyn k)] 
      -> Repr (Dyn k) -> Repr (Dyn k)))
      
  block_ rs ns = pure (\ en -> Block s')
    where
      (v, pas, ns') = buildVis rs
      Vis{local=l,public=s} = dynCheckVis v
      
      g :: [Repr (Dyn k) -> Res (Repr (Dyn k))]
      g = map (\ n -> M.findWithDefault (S.self n) l n) ns'
      
      l' :: Either [MyError] ([Repr (Dyn k)] -> Repr (Dyn k)
      -> M.Map Ident
        (FreeT (M.Map (Key k)) (Either [MyError]) (Repr (Dyn k)))
      l' = vs <&> (\ k en se ->
        M.mapWithKey (\ i f -> let
          FreeT e = fmap (k en se !! f)
          in e <&> (\ fm -> case fm of
            Pure r -> r
            Free m -> S.local i
            
      l' = M.mapWithKey (\ i (FreeT e) -> e <&> (\ fm -> case fm of
        Pure n -> pure (!! n)
        Free m -> S.local i ns <&> (\ f ->
      
      vs
        :: Either [MyError] ([Repr (Dyn k)]
          -> Repr (Dyn k)
          -> [Either [MyError] (Repr (Dyn k))])
      vs = traverse
        (\ (p, f) ->
          f (ns' ++ ns) <&> (\ k en se -> (match p . Just) (k en se)))
        pas
      
      

      
-- | Pattern
type Patt f = Cofree (Decomp f)
newtype Decomp f a = Decomp { getDecomp :: [f a] }
  deriving (Functor, Foldable, Traversable)

instance Monoid w => S.Tuple (Patt (Dyn k) w) where
  type Tup (Patt (Dyn k) w) = Tup k (Patt (Dyn k) w)
  tup_ ts = mempty <: tup_ ts
  
instance S.Tuple (Decomp (Dyn k) a) where
  type Tup (Decomp (Dyn k) a) = Tup k a
  tup_ ts = Decomp [dynCheck (foldMap getTup ts)]
  
instance S.Extend (Patt (Dyn k) a) where
  type Ext (Patt (Dyn k) a) = Decomp (Dyn k) (Patt (Dyn k) a)
  a <: (Decomp ns) # Decomp ns' = a <: Decomp (ns' ++ ns)
    
  
-- | A leaf pattern that can bind the matched value or skip
data Bind = Bind | Skip

bind :: a -> a -> Bind -> a
bind a _ Bind = a
bind _ a Skip = a

type Match r = ReaderT r ((,) [r])

match :: Patt (Dyn k) Bind -> Repr (Dyn k) -> [Repr (Dyn k)]
match (b <: Decomps ds) r = bind xs (r':xs) b
  where
  (xs, r') = runState
    (traverse (state . runReaderT . matchDyn) ds <&> concat)
    r
  
  matchDyn
    :: Dyn k (Patt (Dyn k) Bind)
    -> Match (Repr (Dyn k)) (Repr (Dyn k))
  matchDyn d =
    matchMap (fmap (iterT matchMap') dm)
      <&> (Block . fmap const)
    where
      Dyn dm = fmap
        (\ p ->
          ReaderT (r -> (match p r, Nothing)))
        d
      matchMap' = fmap Just . matchMap
    
  matchMap
    :: (Ord k, Show k)
    => DynMap k
      (Match (Repr (Dyn k)) (Maybe (Self (Dyn k))))
    -> Match (Repr (Dyn k)) (Self (Dyn k))
  matchMap (DynMap e) = ReaderT (\ r -> let
    d = self r
    appendRem m' = M.unionWith mappend
      (M.restrictKeys m' (M.keysSet m))
    split m = traverseMaybeWithKey 
      (\ i (ReaderT f) -> f (d `dynGet` Key i))
    in 
      either
        (pure . DynMap . Left)
        id
        (liftA2
          (\ m m' ->
            split m <&> Dyn . DynMap . Right . appendRem m')
          e
          (getDynMap (getDyn d))))


  
-- | Thread a writer through levels of a tree of paths
newtype Node k w a = Node (FreeT (M.Map (Tag k)) ((,) w) a)
  deriving (Functor, Foldable, Traversable, Applicative, Monad)
  
instance Bifunctor (Node k) where
  bimap f g (Node (FreeT p)) =
    Node (FreeT (bimap f (bimap g (bimap f g)) p))
    
instance Bifoldable (Node k) where
  bifoldMap f g (Node (FreeT p)) =
    bifoldMap f (bifoldMap g (bifoldMap f g)) p
    
instance Bitraversable (Node k) where
  bitraverse f g (Node (FreeT (w, fm))) =
    fmap
      (Node . FreeT)
      (bitraverse f (bitraverse g (bitraverse f g)) p)
  
instance Monoid w => MonadFree ((,) Ident) (Node k w) where
  wrap (i, Node f) = Node (wrap (M.singleton (Key i) f))

instance Monoid (Node k [a] a) where
  mempty = Node (liftF M.empty)
  
  Node (as1, Pure a1) `mappend` Node (as2, fm2    ) =
    Node ([a1] ++ as1 ++ as2, fm2                             )
  Node (as1, fm1)     `mappend` Node (as2, Pure a2) =
    Node (as1 ++ [a2] ++ as2, fm1                             )
  Node (as1, Free m1) `mappend` Node (as2, Free m2) =
    Node (as1 ++ as2        , Free (M.unionWith mappend m1 m2))
  
  
-- | Tree of components
newtype Comps k a = Comps (M.Map (Tag k) (Node k [a] a))

instance Functor (Comps k a) where
  fmap f (Comps m) = Comps (fmap (bimap (fmap f) f) m)
  
instance Foldable (Comps k a) where
  foldMap f (Comps m) = foldMap (bifoldMap (foldMap f) f) m
  
instance Traversable (Comps k a) where
  traverse f (Comps m) =
    fmap Comps (traverse (bitraverse (traverse f) f) m)
  
instance Monoid (Comps k a) where
  mempty = Comps M.empty
  Comps m1 `mappend` Comps m2 = Comps (M.unionWith mappend m1 m2)
  
-- | Generic constructor for a tuple
newtype Tup k a = Tup { getTup :: Comps k a }
  
instance S.Self a => S.Self (Tup k a) where
  self_ i = pun (S.self_ i)
instance S.Local a => S.Local (Tup k a) where
  local_ i = pun (S.local_ i)

instance S.Field a => S.Field (Tup k a) where
  type Compound (Tup k a) = Pun Path (S.Compound a)
  p #. k = pun (p S.#. k)

instance S.Assoc (Tup k a) where
  type Label (Tup k a) = Path
  type Value (Tup k a) = a
  Path f #: a = let (i, m) = f (pure a) in
    Tup (Comps (M.singleton (Key i) m))
 
 
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
newtype Path = Path (forall m a . MonadFree ((,) Ident) m => m a -> (Ident, m a))

instance S.Self Path where self_ i = Path ((,) i)
instance S.Local Path where local_ i = Path ((,) i)
  
instance S.Field Path where
  type Compound Path = Path
  Path f #. i = Path (f . wrap . (,) i)
      
      
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
  Pun p a #. k = Pun (p S.#. k) (a S.#. k)
  
  
-- | A block associates a set of paths partitioned by top-level visibility with values.
-- A public path can be declared without a value,
-- indicating that the path is to be checked for ambiguity but not assigned a value.
data Vis k a = Vis { local :: M.Map Ident a, public :: M.Map (Tag k) a }
--  deriving Functor
  
  
introVis :: a -> P.Vis Path Path -> Vis (Node k [a] a)
introVis a (P.Pub (Path f)) = let (i, m) = f a in 
  Vis{local=M.empty,public=(M.singleton (Key i) m)}
introVis a (P.Priv (Path f)) = let (i, m) = f a in 
  Vis{local=(M.singleton i m),public=M.empty}

instance Monoid a => Monoid (Vis k a) where
  mempty = Vis{local=M.empty,public=M.empty}
  Vis{local=l1,public=s1} `mappend` Vis{local=l2,public=s2} =
    Vis{local=(M.unionWith mappend l1 l2),public=(M.unionWith mappend s1 s2)}

buildVis
  :: [Rec [P.Vis Path Path] a]
  -> (Vis (Node k [Maybe Int] (Maybe Int)), [a], [Ident])
buildVis rs = (r, pas, nub (ns)) where
    
  pas = mapMaybe (\ (Rec (_, pa)) -> pa) rs
  (r, ns) = foldMap (\ (mb, s) -> (introVis mb s, pure (name s))) (enumJust (coerce rs))
  
  name :: P.Vis Path Path -> Ident
  name (P.Pub (Path i _)) = i
  name (P.Priv (Path i _)) = i
  
  enumJust :: [([a], Maybe b)] -> [(Maybe Int, a)]
  enumJust cs = concat (evalState (traverse enumPair cs) 0) where
    
    enumPair (xs, Just _) = 
      traverse (\ a -> state (\ i -> ((Just i, a), i+1))) xs
    enumPair (xs, Nothing) = pure (map ((,) Nothing) xs)
