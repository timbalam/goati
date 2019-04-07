{-# LANGUAGE ExistentialQuantification, FlexibleContexts, GeneralizedNewtypeDeriving, DeriveTraversable, StandaloneDeriving #-}

-- | This module along with 'Goat.Eval.Dyn' contain the core data type representations.
-- This is a pure data representation suitable for optimisation,
-- before conversion to the data type from 'Goat.Eval.Dyn' for evaluation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Syntax.Class'.
module Goat.Repr.Expr
  where

import Goat.Lang.Ident (Ident)
import Goat.Repr.Pattern
import Goat.Util (abstractEither)
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (lift)
import Data.List (elemIndex)
import Data.Text (Text)
import Data.Traversable (fmapDefault, foldMapDefault)
import Bound (Scope(..), Var(..), Bound(..))
  

-- | Runtime value representation
data Repr f a =
    Var a 
  | Repr (Expr (Abs Assoc f) (Repr f) a)
  deriving (Foldable, Traversable)

instance Functor f => Functor (Repr f) where
  fmap = liftM
  
instance Functor f => Applicative (Repr f) where
  pure = Var
  (<*>) = ap

instance Functor f => Monad (Repr f) where
  return = pure
  Repr m >>= f = Repr (m >>>= f)

instance MonadBlock (Abs Assoc f) (Repr f) where
  wrapBlock f = join (Repr (Block f))

-- |
data Expr r m a =
    Number Double
  | Text Text
  | Bool Bool
  | Block (r m a)
  -- | Null
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
 :: Functor m
 => (forall u u' a . (forall a' . u a' -> u' a') -> r u a -> r u' a)
 -> (forall x . m x -> n x)
 -> Expr r m a -> Expr r n a
hoistExpr hoistr f a = case a of 
  Number d -> Number d
  Text t   -> Text t
  Bool b   -> Bool b
  Block r  -> Block (hoistr f r)
  --Null     -> Null
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
  Neg a    -> Neg (f b)

instance (Traversable m, Traversable (r m)) => Functor (Expr r m)
  where 
    fmap = fmapDefault
  
instance (Traversable m, Traversable (r m)) => Foldable (Expr r m) 
  where
    foldMap = foldMapDefault

instance
  (Traversable m, Traversable (r m)) => Traversable (Expr r m)
  where
    traverse f (Number d) = pure (Number d)
    traverse f (Text t) = pure (Text t)
    traverse f (Bool b) = pure (Bool b)
    traverse f (Block r) = Block <$> traverse f r
    --traverse f Null = pure Null
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

instance Bound r => Bound (Expr r) where
  Number d   >>>= _ = Number d
  Text t     >>>= _ = Text t
  Bool b     >>>= _ = Bool b
  Block r    >>>= f = Block (r >>>= f)
  --Null       >>>= _ = Null
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
  

type VarName a b c = 
  Either (Public a) (Either (Local b) c)

blockBindings
 :: MonadBlock (Abs (Pattern (Option (Privacy These)))) m
 => Bindings
      (Multi (Declared Assoc (Privacy These)))
      (Pattern (Option (Privacy These)) ())
      m
      (VarName Ident Ident a)
 -> Abs (Pattern (Option (Privacy These))) m (Var Name b Ident a)
blockBindings b =
  embedBindings
    (blockDeclared


blockDeclared
 :: ( Foldable t
    , MonadBlock (Abs (Pattern (Option (Privacy These)))) m
    )
 => Stores
      t
      (Declared Assoc (Privacy These))
      a
 -> m a
 -> Block (Pattern (Option (Privacy These))) m a
blockDeclared (Stores (Declared (Reveal r) k)) b = Abs lcls
  where
    lcls =
      Closure
        (lp $> pure ())
        (wrapBlock (Abs (Defined (lift <$> lp)))) pcls        
    
    (ns, lp) =
      traverse
        (\ (n, f) -> ([n], f (Right (Left n))))
        (Pattern
          (mapWithKey (toPath k) r)
          (Nothing, const empty))
      where
        toPath k n v = (Just (Local n), p) where
          p = case v of
            Views (That (Local _)) a ->
              iterPaths
                (\ t _ -> foldMap pure t)
                blockNode
                (k a)
            Views _                _ -> leaf
          
          leaf = pure (lift (Scope (return (B (Public n)))))
    
    pcls =
      foldPattern
        (\ f i -> Scope <$> f (B (Local i)))
        (publicPattern
          r
          (foldListPaths
            (\ a _ ->
              unscope . lift . abstractVarName ns <$> toList a) .
            k))
        (lift (lift (lift b)))
      where
        foldListPaths
         :: MonadBlock (Abs r Components) m
         => (a -> b -> [m b])
         -> Paths r a -> b -> [m b]
        foldListPaths f =
          iterPaths
            f
            (\ r k ->
              foldNode r (\ a b -> foldMap pure <$> k a b))
    
    publicPattern
     :: (Traversable r, Foldable t, Monad m)
     => r (These (Public a) (Local a))
     -> (a -> c -> t (Scope (Local c) m b))
     -> Pattern r (c -> Components (Scope (Local c) m b))
    publicPattern r k =
      Pattern
        (mapMaybe (toComponent k) r)
        (pure . Scope . return . B . Local)
      where    
        toComponent
         :: Foldable t
         => (a -> b -> t c)
         -> These (Public a) (Local a)
         -> Maybe (b -> Components c)
        toComponent f (This (Public a)) =
          Just (\ b -> foldMap public (f a b))
        toComponent f (That _) = Nothing
        toComponent f (These (Public a) (Local a')) =
          Just (\ b ->
            foldMap public (f a b) `mappend`
              foldMap local (f a' b))

blockDeclared
 :: ( Foldable t
    , MonadBlock (Abs (Pattern (Option (Privacy These)))) m
    )
 => Stores
      t
      (Declared Assoc (Option (Privacy These)))
      (m (VarName Ident Ident a))
 -> m (VarName p Ident a)
 -> Abs Assoc Field m (VarName p Ident a)
blockDeclared (Stores (Declared (Reveal r) k)) b = Abs lcls
  where
    lcls =
      Closure
        (lp $> pure ())
        (wrapBlock (Abs (Defined (lift <$> lp)))) pcls        
    
    (ns, lp) =
      traverse
        (\ (n, f) -> ([n], f (Right (Left n))))
        (Pattern
          (mapWithKey (toPath k n) r)
          (Nothing, const empty))
      where
        toPath k n th = (Just (Local n), p) where
          p' =
            iterPaths
              (\ a _ ->
                abstractVarName ns <$> publicList (toList a))
              foldNode
              p
          p = case th of
            That (Local x) -> k x
            This (Public _) -> leaf
            These (Public _) _ -> leaf
          leaf = Leaf (pure (return (Left (Public n))))
    
    pcls =
      foldPattern
        (\ f i -> Scope <$> f (B (Local i)))
        (publicPattern
          r
          (foldListPaths
            (\ a _ ->
              unscope . lift . abstractVarName ns <$> toList a) .
            k))
        (lift (lift (lift b)))
      where
        foldListPaths
         :: MonadBlock (Abs r Components) m
         => (a -> b -> [m b])
         -> Paths r a -> b -> [m b]
        foldListPaths f =
          iterPaths
            f
            (\ r k ->
              foldNode r (\ a b -> foldMap pure <$> k a b))
    
    publicPattern
     :: (Traversable r, Foldable t, Monad m)
     => r (These (Public a) (Local a))
     -> (a -> c -> t (Scope (Local c) m b))
     -> Pattern r (c -> Components (Scope (Local c) m b))
    publicPattern r k =
      Pattern
        (mapMaybe (toComponent k) r)
        (pure . Scope . return . B . Local)
      where    
        toComponent
         :: Foldable t
         => (a -> b -> t c)
         -> These (Public a) (Local a)
         -> Maybe (b -> Components c)
        toComponent f (This (Public a)) =
          Just (\ b -> foldMap public (f a b))
        toComponent f (That _) = Nothing
        toComponent f (These (Public a) (Local a')) =
          Just (\ b ->
            foldMap public (f a b) `mappend`
              foldMap local (f a' b))

abstractVarName
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) (Scope (Public p) m) (VarName q a b)
abstractVarName ns m =
  Scope
    (Scope
      (m >>= \ a -> case a of
        Left p -> B p
        Right (Left (Local n)) -> case elemIndex (Just n) ns of
          Just i -> F (return (B (Local i)))
          Nothing -> F (return (Right (Left (Local n))))
        Right (Right x) ->
          F (return (F (return (Right (Right x)))))))

newtype Super a = Super { getSuper :: a }

      
blockPaths
 :: Monoid s
 => (a -> Matchings [] s m) -> Paths Assoc a -> Matchings [] s m
blockPaths k =
  mergeMatchings .
    iterPaths
      k
      (\ r k ->
        blockNode r (pure . mergeMatchings . k) . return)
  where
    mergeMatchings = these id id (<>)

blockNode
 :: (MonadBlock (Abs (Pattern s)) m, Monoid s, Applicative h)
 => Assoc a
 -> (a -> Views s (Matchings [] s m))
 -> m b
 -> Bindings h (Pattern s) m b
blockNode r k b =
  foldMatchings
    (Extend
      (Reveal (k <$> r))
      (pure . return)
    

foldNode
 :: ( Traversable r, Applicative f
    , MonadBlock (Abs r f) m, Applicative g
    )
 => r a -> (a -> b -> f (m b)) -> b -> g (m b)
foldNode r k b = pure (wrapBlock (Abs cls)) where
  cls =
    foldPattern
      (\ f i -> Scope <$> f (B (Local i)))
      (nodePattern r k)
      b

foldMatchings
 :: (Traversable r, Alternative f)
 => Extend (Reveal Assoc s) (Matchings [] s m)
 -> m a
 -> Block (Pattern s) m a
foldPattern r a =
  Let pf (lift a) (Define rf)
  where
    pf = Decons (fst <$> rfa)
    rf = mapWithIndex (\ i (_, f) -> f i) r
          lift (f i) >>= Scope . return . B . Local)
        rfa



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