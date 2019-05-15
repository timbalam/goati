{-# LANGUAGE ExistentialQuantification, FlexibleContexts, GeneralizedNewtypeDeriving, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, RankNTypes #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang'.
module Goat.Repr.Expr
  where

import Goat.Lang.Ident (Ident)
import Goat.Repr.Assoc
import Goat.Repr.Pattern
import Goat.Util (abstractEither)
import Control.Applicative (Alternative(..), Const(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.Bifunctor
import Data.Functor (($>))
import Data.These (these, These(..))
import Data.List (elemIndex)
import Data.Text (Text)
import Data.Traversable (fmapDefault, foldMapDefault)
import qualified Data.Monoid as Monoid (Alt(..))
import Data.Semigroup (Option(..))
import Data.Functor.Plus (Plus(..))
import Bound (Scope(..), Var(..), Bound(..))
import Bound.Scope (hoistScope, abstract)
  

-- | Runtime value representation
data Repr f a =
    Var a 
  | Repr (Expr f (Repr f) a)
  deriving (Foldable, Traversable)

emptyRepr :: Repr f a
emptyRepr = Repr Null

instance Functor f => Functor (Repr f) where
  fmap = liftM
  
instance Functor f => Applicative (Repr f) where
  pure = Var
  (<*>) = ap

instance Functor f => Monad (Repr f) where
  return = pure
  Repr m >>= f = Repr (m >>>= f)

instance Functor f => MonadBlock (Abs f) (Repr f) where
  wrapBlock f = Repr (Block f)

-- |
data Expr f m a =
    Number Double
  | Text Text
  | Bool Bool
  | Block (Abs f m a)
  | Null
  | m a :#. Ident
  | m a :#+ m a
  | m a :#- m a
  | m a :#* m a
  | m a :#/ m a
  | m a :#^ m a
  | m a :#== m a
  | m a :#!= m a
  | m a :#< m a
  | m a :#<= m a
  | m a :#> m a
  | m a :#>= m a
  | m a :#|| m a
  | m a :#&& m a
  | Not (m a)
  | Neg (m a)

hoistExpr
 :: (Functor r, Functor m)
 => (forall x . m x -> n x) -> Expr r m a -> Expr r n a
hoistExpr f a = case a of 
  Number d -> Number d
  Text t   -> Text t
  Bool b   -> Bool b
  Block r  -> Block (hoistAbs f r)
  Null     -> Null
  a :#. n  -> f a :#. n
  a :#+ b  -> f a :#+ f b
  a :#- b  -> f a :#- f b
  a :#* b  -> f a :#* f b
  a :#/ b  -> f a :#/ f b
  a :#^ b  -> f a :#^ f b
  a :#== b -> f a :#== f b
  a :#!= b -> f a :#!= f b
  a :#< b  -> f a :#< f b
  a :#<= b -> f a :#<= f b
  a :#> b  -> f a :#> f b
  a :#>= b -> f a :#>= f b
  a :#|| b -> f a :#|| f b
  a :#&& b -> f a :#&& f b
  Not a    -> Not (f a)
  Neg a    -> Neg (f a)

instance (Traversable m, Traversable r) => Functor (Expr r m)
  where 
    fmap = fmapDefault
  
instance (Traversable m, Traversable r) => Foldable (Expr r m) 
  where
    foldMap = foldMapDefault

instance
  (Traversable m, Traversable r) => Traversable (Expr r m)
  where
    traverse f (Number d) = pure (Number d)
    traverse f (Text t) = pure (Text t)
    traverse f (Bool b) = pure (Bool b)
    traverse f (Block r) = Block <$> traverse f r
    traverse f Null = pure Null
    --traverse f (a :# b) = (:#) <$> traverse f a <*> traverse f b
    traverse f (a :#. n) = (:#. n) <$> traverse f a
    traverse f (a :#+ b) = (:#+) <$> traverse f a <*> traverse f b
    traverse f (a :#- b) = (:#-) <$> traverse f a <*> traverse f b
    traverse f (a :#* b) = (:#*) <$> traverse f a <*> traverse f b
    traverse f (a :#/ b) = (:#/) <$> traverse f a <*> traverse f b
    traverse f (a :#^ b) = (:#^) <$> traverse f a <*> traverse f b
    traverse f (a :#== b) = (:#==) <$> traverse f a <*> traverse f b
    traverse f (a :#!= b) = (:#!=) <$> traverse f a <*> traverse f b
    traverse f (a :#> b) = (:#>) <$> traverse f a <*> traverse f b
    traverse f (a :#>= b) = (:#>=) <$> traverse f a <*> traverse f b
    traverse f (a :#< b) = (:#<) <$> traverse f a <*> traverse f b
    traverse f (a :#<= b) = (:#<=) <$> traverse f a <*> traverse f b
    traverse f (a :#|| b) = (:#||) <$> traverse f a <*> traverse f b
    traverse f (a :#&& b) = (:#&&) <$> traverse f a <*> traverse f b
    traverse f (Not a) = Not <$> traverse f a
    traverse f (Neg a) = Neg <$> traverse f a

instance Functor r => Bound (Expr r) where
  Number d   >>>= _ = Number d
  Text t     >>>= _ = Text t
  Bool b     >>>= _ = Bool b
  Block r    >>>= f = Block (r >>>= f)
  Null       >>>= _ = Null
  --(a :# b)   >>>= f = (a >>= f) :# (b >>= f)
  (a :#. n)  >>>= f = (a >>= f) :#. n
  (a :#+ b)  >>>= f = (a >>= f) :#+ (b >>= f)
  (a :#- b)  >>>= f = (a >>= f) :#- (b >>= f)
  (a :#* b)  >>>= f = (a >>= f) :#* (b >>= f)
  (a :#/ b)  >>>= f = (a >>= f) :#/ (b >>= f)
  (a :#^ b)  >>>= f = (a >>= f) :#^ (b >>= f)
  (a :#== b) >>>= f = (a >>= f) :#== (b >>= f)
  (a :#!= b) >>>= f = (a >>= f) :#!= (b >>= f)
  (a :#> b)  >>>= f = (a >>= f) :#> (b >>= f)
  (a :#>= b) >>>= f = (a >>= f) :#>= (b >>= f)
  (a :#< b)  >>>= f = (a >>= f) :#< (b >>= f)
  (a :#<= b) >>>= f = (a >>= f) :#<= (b >>= f)
  (a :#|| b) >>>= f = (a >>= f) :#|| (b >>= f)
  (a :#&& b) >>>= f = (a >>= f) :#&& (b >>= f)
  Not a      >>>= f = Not (a >>= f)
  Neg a      >>>= f = Neg (a >>= f)

--
  
 
-- | Access controlled labels
newtype Public a = Public { getPublic :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)
newtype Local a = Local { getLocal :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)
newtype Match a = Match { getMatch :: a }
  deriving (Functor, Foldable, Traversable, Semigroup, Monoid)

type Privacy p = p (Public ()) (Local ())

data Views s a = Views s a
  deriving (Functor, Foldable, Traversable)

instance Monoid s => Applicative (Views s) where
  pure a = Views mempty a
  Views s1 f <*> Views s2 a = Views (s1 `mappend` s2) (f a)

instance (Monoid s, Monoid a) => Monoid (Views s a) where
  mempty = Views mempty mempty
  Views s1 a1 `mappend` Views s2 a2 =
    Views (s1 `mappend` s2) (a1 `mappend` a2)

instance Bifunctor Views where
  bimap f g (Views s a) = Views (f s) (g a)

instance Biapplicative Views where
  bipure s a = Views s a
  Views f g <<*>> Views s a = Views (f s) (g a)
  
instance Bifoldable Views where
  bifoldMap f g (Views s a) = f s `mappend` g a
    
instance Bitraversable Views where
  bitraverse f g (Views s a) = Views <$> f s <*> g a

bicrosswalkViews
 :: Semigroup s
 => (a -> Views s c)
 -> (b -> Views s d)
 -> These a b
 -> Views s (These c d)
bicrosswalkViews f g (This a) = This <$> f a
bicrosswalkViews f g (That b) = That <$> g b
bicrosswalkViews f g (These a b) =
  bimap (<>) These (f a) <<*>> g b

newtype Reveal r s a = Reveal (r (Views s a))
  deriving (Functor, Foldable, Traversable)

hoistReveal
 :: (forall x . q x -> r x)
 -> Reveal q s a -> Reveal r s a
hoistReveal f (Reveal r) = Reveal (f r)

instance Functor r => Bifunctor (Reveal r) where
  bimap f g (Reveal r) = Reveal (bimap f g <$> r)

instance Foldable r => Bifoldable (Reveal r) where
  bifoldMap f g (Reveal r) = foldMap (bifoldMap f g) r

instance Traversable r => Bitraversable (Reveal r) where
  bitraverse f g (Reveal r) =
    Reveal <$> traverse (bitraverse f g) r

instance (Align r, Semigroup s) => Align (Reveal r s) where
  nil = Reveal nil
  
  align (Reveal ra) (Reveal rb) =
    Reveal (alignWith (bicrosswalkViews id id) ra rb)


  

type VarName a b c = 
  Either (Public a) (Either (Local b) c)

blockBindings
 :: MonadBlock (Abs (Pattern (Option (Privacy These)))) m
 => Bindings
      (Multi (Declared Assoc (Privacy These)))
      (Pattern (Option (Privacy These)) ())
      m
      (VarName Ident Ident a)
 -> m (VarName b Ident a)
 -> m (VarName b Ident a)
blockBindings dm b =
  wrapBlock (Abs (Let px (lift penv) (Let lx lenv self)))
  where
    -- local and public bindings
    lpdm =
      transBindings
        (partitionDeclared
          (\ a -> case a of That (Local _) -> False; _ -> True))
        dm
    -- local pattern
    (lx, ls) =
      squashBindings <$>
        transverseBindings
          blockDeclared
          (hoistBindings
            lift
            (transBindings (\ (Parts f _) -> f) lpdm))
    (lns, lpenv) = getLocal (getNames lx)
    
    -- public bindings
    pdm = transBindings (\ (Parts _ g) -> g) lpdm
    (px, ps) = 
      squashBindings <$>
        transverseBindings blockDeclared (hoistBindings lift pdm)
    pn = getNames px
    (pns, ppenv) = getLocal pn
    pfself = getPublic pn
        
    self =
      inheritSuper
        px
        b 
        (abstractVarName pns lns . return <$> ps)
    
    lenv =
      localEnvironment
        lx
        lpenv
        (abstractVarName pns lns . return <$> ls)
        
    
    -- punned paths scope to parent environments
    (ppx, pps) =
      getConst (transverseBindings (Const . punDeclared) pdm)
    
    penv = publicEnvironment ppx pfself ppenv pps
    
    
    inheritSuper
     :: Monad m
     => Pattern s ()
     -> m a
     -> Block
          (Pattern s)
          (Scope (Local Int) m)
          (Scope b1 (Scope b2 (Scope b3 m)) a)
     -> Block
          (Pattern s)
          (Scope b1 (Scope b2 (Scope b3 m)))
          a
    inheritSuper p sup m =
      hoistBindings (lift . lift . lift) m' >>>= id
      where
        m' = Let p (return (lift (lift (lift sup)))) m
    
    localEnvironment
     :: MonadBlock (Abs (Pattern s)) m
     => Pattern s ()
     -> m a
     -> Block
          (Pattern s)
          (Scope (Local Int) m)
          (Scope b1 (Scope b2 (Scope b3 m)) a)
     -> Scope b1 (Scope b2 (Scope b3 m)) a
    localEnvironment p penv m =
      join (lift (lift (lift val)))
      where
        m' = Let p (return (lift (lift (lift penv)))) m
        val = wrapBlock (Abs (hoistBindings lift m'))
    
    publicEnvironment
     :: MonadBlock (Abs (Pattern s)) m 
     => Pattern s ()
     -> Scope b m a
     -> m a
     -> Block
          (Pattern s)
          (Scope (Local Int) (Scope (Local Int) m))
          (Scope b m a)
     -> Scope b m a
    publicEnvironment p self penv m =
      join (lift val)
      where
        min = Let p (return (lift penv)) m
        mout = Let p (return self) min
        val = wrapBlock (Abs (hoistBindings lift mout))
    
    getNames
     :: Monoid s
     => Pattern s a
     -> Extend (Reveal Assoc s) (Maybe Ident)
    getNames (Stores (Extend (Reveal r) _)) =
      Extend
        (Reveal (mapWithKey (\ n _ -> pure (Just n)) r))
        Nothing
    
    getLocal
     :: MonadBlock (Abs (Pattern s)) m
     => Extend (Reveal Assoc s) (Maybe Ident)
     -> ([Maybe Ident], m (VarName b Ident c))
    getLocal xr =
      wrapBlock . Abs . Define . Stores <$>
        traverse (\ n -> ([n], localVar n)) xr
      where
        localVar = maybe empty (pure . return . Right . Left . Local)
    
    getPublic
     :: MonadBlock (Abs (Pattern s)) m
     => Extend (Reveal Assoc s) (Maybe Ident)
     -> Scope (Public Ident) m a
    getPublic xr = 
      Scope (wrapBlock (Abs (Define (Stores (publicVar <$> xr)))))
      where
        publicVar =
          maybe
            empty
            (pure . return . B . Public)


partitionDeclared 
 :: (s -> Bool)
 -> Stores g (Declared Assoc s) a
 -> Parts
      (Stores g (Declared Assoc s))
      (Stores g (Declared Assoc s))
      a
partitionDeclared p (Stores (Declared (Reveal r) k)) =
  Parts
    (Stores (Declared (Reveal lr) k))
    (Stores (Declared (Reveal rr) k))
  where
    (lr, rr) =
      mapEither
        (\ (Views s a) ->
          if p s then
            Right (Views s a) else
            Left (Views s a))
        r
      
blockDeclared
 :: MonadBlock (Abs (Pattern (Option (Privacy These)))) m
 => Multi (Declared Assoc (Privacy These)) a
 -> ( Pattern (Option (Privacy These)) ()
    , Bindings
        (Pattern (Option (Privacy These)))
        (Pattern (Option (Privacy These)) ())
        (Scope (Local Int) m)
        a
    )
blockDeclared (Stores (Declared (Reveal r) k)) =
  bindingParts
    r
    (bimap pure (blockPaths blockLeaf blockNode . k))

blockLeaf
 :: (Foldable t, Alternative g, Monad m)
 => t a -> b -> g (m a)
blockLeaf t _ = Monoid.getAlt (foldMap (pure . return) t)

blockNode
 :: (MonadBlock (Abs (Pattern s)) m, Monoid s)
 => Pattern s ()
 -> Block (Pattern s) (Scope (Local Int) m) a
 -> Int
 -> [Scope (Local Int) m a]
blockNode pg m i = 
  [Scope (wrapBlock (Abs (hoistBindings lift m')))]
  where
    m' = Let pg (return (B (Local i))) (F . return <$> m)

punDeclared
 :: ( Foldable t
    , MonadBlock (Abs (Pattern (Option (Privacy These)))) m
    )
 => Stores t (Declared Assoc (Privacy These)) a
 -> ( Pattern (Option (Privacy These)) ()
    , Bindings
        (Pattern (Option (Privacy These)))
        (Pattern (Option (Privacy These)) ())
        (Scope (Local Int) (Scope (Local Int) m))
        b
    )
punDeclared (Stores (Declared (Reveal r) k)) =
  bindingParts
    r
    (bimap pure (blockPaths punLeaf punNode . k))

-- | 'punLeaf p v i' returns a value obtained from the inner scoped parent
punLeaf
 :: (Monad m, Applicative g)
 => a -> Int -> g (Scope b (Scope (Local Int) m) c)
punLeaf _ i = pure (lift (Scope (return (B (Local i)))))

-- | 'punNode p v i' generates a value which binds two versions of 'i'
punNode
 :: (MonadBlock (Abs (Pattern s)) m, Monoid s) 
 => Pattern s ()
 -> Block (Pattern s) (Scope (Local Int) (Scope (Local Int) m)) b
 -> Int
 -> [Scope (Local Int) (Scope (Local Int) m) b]
punNode pg m i =
  [Scope (Scope (wrapBlock (Abs (hoistBindings lift mouter))))]
  where
    m' = inner (outer (F . return . F . return <$> m))
    -- bind outer scope of 'm' to fields of outer scope
    outer = Let pg (return (F (return (B (Local i)))))
    -- bind inner scope of 'm' to fields of inner scope
    inner = Let pg (return (B (Local i)))

-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVarName
 :: (Monad m, Eq a)
 => [Maybe a]
 -> [Maybe a]
 -> m (VarName p a b)
 -> Scope
      (Local Int)
      (Scope (Local Int) (Scope (Public p) m))
      (VarName q a b)
abstractVarName outs ins m =
  Right <$> 
    abstractLocal outs (abstractLocal ins (abstractPublic m))
  where
    abstractPublic = abstractEither id
    abstractLocal ns =
      abstract (\ a -> case a of
        Left (Local n) -> Local <$> elemIndex (Just n) ns
        Right _ -> Nothing)

-- | 'blockPaths ka kp pths i' generates a value from set of paths 'pths'.
-- The leaf generator 'ka' is applied to leaves.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
blockPaths
 :: (Monad m, Monoid s)
 => (a -> Int -> [Scope (Local Int) m b])
 -> (Pattern s () ->
      Block (Pattern s) (Scope (Local Int) m) b ->
      Int ->
      [Scope (Local Int) m b])
 -> Paths Assoc a -> Int -> [Scope (Local Int) m b]
blockPaths ka kp =
  mergeMatchings .
    iterPaths
      ka
      (\ r k ->
        uncurry
          kp
          (bindingParts r (pure . mergeMatchings . k)))
  where
    mergeMatchings = these id id mappend

-- | 'bindingParts r k' generates a pattern matching the fields of 'Assoc' 'r' and a corresponding binding value with identical fields with values generated by the fields of 'r'.
bindingParts
 :: (Monoid s, Monad m)
 => Assoc a
 -> (a -> Views s (Int -> [Scope (Local Int) m b]))
 -> (Pattern s (), Bindings (Pattern s) p (Scope (Local Int) m) b)
bindingParts r k = (pg, Define xg)
  where
    x =
      Extend
        (Reveal (k <$> r))
        (pure . Scope . return . B . Local)
    pg = Stores (x $> pure ())
    xg = Stores (mapWithIndex (\ i f -> f i) x)


-- | Marker type for self- and env- references
newtype Extern a = Extern { getExtern :: a }


{-
data Versions f m a =
    Null
  | Current (f (m a)) (Versions f m a)
  | m a :# Verions f (Scope (Super ()) m) a
  deriving (Functor, Foldable, Traversable)

instance Functor f => Bound (Versions f) where
  Null          >>>= f = Null
  Current fm vs >>>= f = Current (fmap (>>= f) fm) (p >>>= f)
  m :# vs       >>>= f = (m >>= f) :# (vs >>>= f)  

-- | Permit bindings with a default value 
data Request a = Must a | Can a
  deriving (Eq, Show)

nec :: (a -> b) -> (a -> b) -> Nec a -> b
nec f _ (Req a) = f a
nec _ g (Opt a) = g a


toEval
 :: ( S.IsString k, Ord k
    , Foldable f, Applicative f )
 => Repr k (Dyn' k)
      (Free (Repr k (Dyn' k)) (P.Name P.Ident (Nec P.Ident)))
 -> Synt (Res k) (Eval (Dyn k f))
toEval r =
  freeToEval (fmap (iter (S.esc_ . freeToEval) . fmap varToEval) r)
  where
    varToEval (P.Ex (P.Use n))        = S.use_ n
    varToEval (P.In (P.Pub Nothing))  = S.fromString ""
    varToEval (P.In (P.Pub (Just n))) = S.ident S.fromString n
    varToEval (P.In (P.Priv n))       =
      nec (S.ident S.fromString) opt n
    
    freeToEval r = Synt (traverse readSynt r
      <&> fmap iterExpr . sequenceA)
    
    opt n = Synt (reader (maybe
      (pure r0)
      (\ f -> reader (f . snd))
        . handleEnv n
        . snd))
      
    r0 :: Applicative f => Eval.Repr (Dyn k f)
    r0 = (Eval.Repr
      . Block
      . const
      . dyn)
        (DynMap Nothing M.empty)
        
        
unopExpr
 :: (Foldable f, Applicative f)
 => S.Unop
 -> Eval.Repr (Dyn k f)
 -> Eval.Repr (Dyn k f)
unopExpr S.Neg = S.neg_
unopExpr S.Not = S.not_

binopExpr
 :: (Foldable f, Applicative f)
 => S.Binop
 -> Eval.Repr (Dyn k f)
 -> Eval.Repr (Dyn k f)
 -> Eval.Repr (Dyn k f)
binopExpr S.Add = (S.#+)
binopExpr S.Sub = (S.#-)
binopExpr S.Prod = (S.#*)
binopExpr S.Div = (S.#/)
binopExpr S.Pow = (S.#^)
binopExpr S.Eq = (S.#==)
binopExpr S.Ne = (S.#!=)
binopExpr S.Lt = (S.#<)
binopExpr S.Le = (S.#<=)
binopExpr S.Gt = (S.#>)
binopExpr S.Ge = (S.#>=)
binopExpr S.Or = (S.#||)
binopExpr S.And = (S.#&&)
        
iterExpr
 :: (Ord k, Foldable f, Applicative f)
 => Repr k (Dyn' k) (Eval.Repr (Dyn k f)) -> Eval.Repr (Dyn k f)
iterExpr (Var r) = r
iterExpr (Repr (Number d)) = Eval.Repr (Number d)
iterExpr (Repr (Text t))   = Eval.Repr (Text t)
iterExpr (Repr (Bool b))   = Eval.Repr (Bool b)
iterExpr (Repr (Block e))  = case e of
  m `At` k        -> self (iterExpr m) `dynLookup` k
  m1 `Update` m2  -> iterExpr m1 S.# iterExpr m2
  Unop op m       -> unopExpr op (iterExpr m)
  Binop op m1 m2  -> binopExpr op (iterExpr m1) (iterExpr m2)
  Lift dkv        -> (Eval.Repr
    . Block
    . const
    . dyn
    . runDyn')
      (fmap iterExpr dkv)
  Abs pas en' dkv -> abs pas en' dkv
  where
    abs pas en' dkv = Eval.Repr (Block k)
      where
        k se = (dyn . runDyn') (fmap instantiate' dkv)
          where
            instantiate' = iterExpr . instantiate (ref (rvs'!!) (ren'!!) rse)
            
            rse = Var se
            rvs' = foldMap
              (\ (p, a) -> map Var (match p (instantiate' a)))
              pas
            ren' = map (Var . instantiate') en'

instance (Ord k, Functor f)
  => Applicative (Repr k f) where
  pure = Var
  (<*>) = ap
  
instance (Ord k, Functor f) => Monad (Repr k f) where
  return = pure
  Var a  >>= f = f a
  Repr v >>= f = Repr (fmap (>>>= f) v)

instance (Ord k, Functor f, Eq1 f, Eq a)
  => Eq (Repr k f a) where
  Var a == Var a' = a == a'
  Repr v == Repr v' = v == v'
  
instance (Ord k, Functor f, Eq1 f) => Eq1 (Repr k f) where
  (==#) = (==)

instance (Ord k, Functor f, Eq1 f, Monad m, Eq1 m, Eq a)
  => Eq (Repr k f m a) where
  m `At` k           == m' `At` k'       =
    m ==# m' && k == k'
  (m1 `Update` m2) == (m1' `Update` m2') =
    m1 ==# m1' && m2 ==# m2'
  Abs ps en kv     == Abs ps' en' kv'    =
    ps ==# ps' && en ==# en' && kv ==# kv'
  Lift kv          == Lift kv'           =
    fmap Lift1 kv ==# fmap Lift1 kv'
  Unop op m        == Unop op' m'        = op == op' && m ==# m'
  Binop op m1 m2   == Binop op' m1' m2'  = op == op' &&
    m1 ==# m2 && m1' ==# m2'
  _                == _                  = False
  
instance (Ord k, Functor f, Eq1 f, Monad m, Eq1 m) 
  => Eq1 (Repr k f m) where
  (==#) = (==)
    
    
instance (Ord k, Show k, Functor f, Show1 f, Show a)
  => Show (Repr k f a) where
  showsPrec d (Var a) = showsUnaryWith showsPrec "Var" d a
  showsPrec d (Repr v) = showsUnaryWith showsPrec "Repr" d v
  
instance (Ord k, Show k, Functor f, Show1 f)
  => Show1 (Repr k f) where
  showsPrec1 = showsPrec
 
instance (Ord k, Show k, Functor f, Show1 f, Monad m, Show1 m, Show a)
  => Show (Repr k f m a) where
  showsPrec d e = case e of
    m `At` x       ->
      showsBinaryWith showsPrec1 showsPrec "At" d m x
    m1 `Update` m2 ->
      showsBinaryWith showsPrec1 showsPrec1 "Concat" d m1 m2
    Abs pas en kv  ->
      showsTrinaryWith showsPrec1 showsPrec
        showsPrec1 "Abs" d pas en kv
    Lift kv        ->
      showsUnaryWith showsPrec1 "Lift" d (fmap Lift1 kv)
    Unop op m      ->
      showsBinaryWith showsPrec showsPrec1 "Unop" d op m
    Binop op m1 m2 ->
      showsTrinaryWith showsPrec showsPrec1
        showsPrec1 "Binop" d op m1 m2
    
instance (Ord k, Show k, Functor f, Show1 f, Monad m, Show1 m)
  => Show1 (Repr k f m) where
  showsPrec1 = showsPrec
 
 
instance S.IsString a => S.IsString (Nec a) where
  fromString i = Req (S.fromString i)
  
nume = error "Num (Repr k f a)"

instance Applicative m => Num (Synt m (Repr k f a)) where
  fromInteger = Synt . pure . Repr . fromInteger
  (+) = nume
  (-) = nume
  (*) = nume
  abs = nume
  signum = nume
  negate = nume
  
frace = error "Frac (Repr k f a)"
  
instance Applicative m => Fractional (Synt m (Repr k f a)) where
  fromRational = Synt . pure . Repr . fromRational
  (/) = frace
  
instance Applicative m => S.Text_ (Synt m (Repr k f a)) where
  quote_ = Synt . pure . Repr . S.quote_

syntUnop
 :: Applicative m
 => S.Unop -> Synt m (Repr k f a) -> Synt m (Repr k f a)
syntUnop op (Synt m) = Synt (fmap (Repr . Block . Unop op) m)

syntBinop
 :: Applicative m
 => S.Binop
 -> Synt m (Repr k f a)
 -> Synt m (Repr k f a)
 -> Synt m (Repr k f a)
syntBinop op (Synt m) (Synt m') = Synt (liftA2 (binop' op) m m')
    where
      binop' op x y = Repr (Block (Binop op x y))
      
instance Applicative m => S.ArithB_ (Synt m (Repr k f a)) where
  (#+) = syntBinop S.Add
  (#-) = syntBinop S.Sub
  (#*) = syntBinop S.Prod
  (#/) = syntBinop S.Div
  (#^) = syntBinop S.Pow
  
instance Applicative m => S.CmpB_ (Synt m (Repr k f a)) where
  (#==) = syntBinop S.Eq
  (#!=) = syntBinop S.Ne
  (#<)  = syntBinop S.Lt
  (#<=) = syntBinop S.Le
  (#>)  = syntBinop S.Gt
  (#>=) = syntBinop S.Ge

instance Applicative m => S.LogicB_ (Synt m (Repr k f a)) where
  (#||) = syntBinop S.Or
  (#&&) = syntBinop S.And

instance Applicative m => S.Unop_ (Synt m (Repr k f a)) where
  neg_ = syntUnop S.Neg
  not_ = syntUnop S.Not
  
instance (Functor f, S.Extern a) => S.Extern_ (Free (Repr k f) a) where
  use_ n = pure (S.use_ n)
  
instance (Applicative m, S.Extern a)
  => S.Extern_ (Synt m (Repr k f a)) where
  use_ n = (Synt . pure . Var) (S.use_ n)
  
instance (Applicative m, S.IsString a) => S.IsString (Synt m (Repr k f a)) where
  fromString n = (Synt . pure . Var) (S.fromString n)
  
instance (Functor f, S.IsString a) => S.IsString (Free (Repr k f) a) where
  fromString n = pure (S.fromString n)
  
instance (Applicative m, S.IsString k) => S.Field_ (Synt m (Repr k f a)) where
  type Compound (Synt m (Repr k f a)) =
    Synt m (Repr k f a)
  Synt m #. n = Synt (m <&> (\ r ->
    (Repr . Block) (r `At` S.ident S.fromString n)))

instance (Applicative m, Functor f)
 => S.Esc_ (Synt m (Repr k f (Free (Repr k f) a))) where
  type Lower (Synt m (Repr k f (Free (Repr k f) a))) =
    Synt m (Repr k f (Free (Repr k f) a))
  esc_ (Synt m) = Synt (fmap (Var . wrap) m)
  
instance (MonadWriter [StaticError k] m, S.IsString k, Ord k)
 => S.Block_
      (Synt m
        (Repr k
          (Dyn' k)
          (Free
            (Repr k (Dyn' k))
            (P.Name k (Nec P.Ident))))) where
  type Stmt
    (Synt m
      (Repr k (Dyn' k)
        (Free
          (Repr k (Dyn' k))
          (P.Name k (Nec P.Ident))))) =
      Stmt [P.Vis (Path k) (Path k)]
        (Patt (Matches k) Bind, Synt m
          (Repr k (Dyn' k) (Free
            (Repr k (Dyn' k))
            (P.Name k (Nec P.Ident)))))
      
  block_ rs = Synt (liftA2 exprBlock
    (dynCheckVis v)
    (traverse
      (bitraverse dynCheckPatt readSynt)
      pas))
    where
      (v, pas) = buildVis rs
      ns' = nub (foldMap (\ (Stmt (ps, _)) -> map name ps) rs)
      
      name :: P.Vis (Path k) (Path k) -> P.Ident
      name (P.Pub (Path n _)) = n
      name (P.Priv (Path n _)) = n
      
      
      exprBlock (Vis{private=l,public=s}) pas = Repr (Block e)
        where
          e
           :: Repr k (Dyn' k) (Repr k (Dyn' k))
                (Free (Repr k (Dyn' k)) (P.Name k (Nec P.Ident)))
          e = Abs pas' localenv (dyn kv) where
            kv = DynMap Nothing (M.map
              (fmap (Scope . Var . B . Match))
              s)
              
            pas' = map (fmap abstract') pas
            
          abstract'
           :: Repr k (Dyn' k)
                (Free (Repr k (Dyn' k)) (P.Name k (Nec P.Ident)))
           -> Scope Ref (Repr k (Dyn' k))
                (Free (Repr k (Dyn' k)) (P.Name k (Nec P.Ident)))
          abstract' m = Scope (m >>= \ a -> case runFree a of
            Pure (P.Ex e) ->
              (Var . F . Var . pure) (P.Ex e)
            
            Pure (P.In (P.Pub Nothing)) ->
              Var (B Self)
              
            Pure (P.In (P.Pub (Just k))) ->
              (Repr . Block) (Var (B Self) `At` k)
              
            Pure (P.In (P.Priv n)) ->
              maybe
                ((Var . F . Var . pure . P.In) (P.Priv n))
                (Var . B . Env)
                (elemIndex (nec id id n) ns')
                
            Free r ->
              Var (F r))
            
          localenv
           :: (S.IsString k, S.IsString a)
           => [Scope Ref (Repr k (Dyn' k)) a]
          localenv = en' where
            en' = map
              (\ n -> M.findWithDefault
                ((Scope . Repr . Block)
                  (Var (B Self) `At` S.ident S.fromString n))
                n
                lext)
              ns'
              
            -- extend inherited local bindings
            lext = M.mapWithKey
              (\ n m -> case runFree (fmap (Var . B . Match) m) of
                Pure r -> Scope r
                Free dkv -> 
                  (Scope . Repr . Block) 
                    ((Var . F . Var) (S.ident S.fromString n)
                    `Update`
                    (Repr . Block . Lift) (dyn dkv)))
              l
      
instance (Applicative m, Ord k)
 => S.Extend_ (Synt m (Repr k f a)) where
  type Ext (Synt m (Repr k f a)) = Synt m (Repr k f a)
   
  Synt m # Synt m' = Synt (liftA2 ext' m m') where
    ext' m m' = Repr (Block (m `Update` m'))
-}