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


data Expr r m a =
    Number Double
  | Text Text
  | Bool Bool
  | Abs (r (Scope (Public Ident) m) a)
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
  Abs r    -> Abs (hoistr (hoistScope f) r)
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

instance
  (Traversable m, Traversable (r (Scope (Public ()) m)))
   => Functor (Expr r m)
  where 
    fmap = fmapDefault
  
instance
  (Traversable m, Traversable (r (Scope (Public ()) m)))
   => Foldable (Expr r m) 
  where
    foldMap = foldMapDefault

instance
  (Traversable m, Traversable (r (Scope (Public ()) m)))
   => Traversable (Expr r m)
  where
    traverse f (Number d) = pure (Number d)
    traverse f (Text t) = pure (Text t)
    traverse f (Bool b) = pure (Bool b)
    traverse f (Abs r) = Abs <$> traverse f r
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
  Abs r      >>>= f = Abs (r >>>= f)
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

data Abs r f m a =
    Block (Pattern r (f (m a)))
  | Closure
      (Pattern r (f ()))
      (Scope (Local Int) m a)
      (Abs r f (Scope (Local Int) m) a)
  deriving (Functor, Foldable, Traversable)

hoistAbs
 :: (Functor r, Functor f, Functor m)
 => (forall x . m x -> n x)
 -> Abs r f m a
 -> Abs r f n a
hoistAbs f (Block r) = Block (fmap f <$> r)
hoistAbs f (Closure p a b) =
  Closure p (hoistScope f a) (hoistAbs (hoistScope f) b)
  
{-
instance (Functor r, Functor m) => Functor (Abs r m) where
  fmap f (Abs r) = Abs (fmap (fmap f) r)

instance (Foldable r, Foldable m) => Foldable (Abs r m) where
  foldMap f (Abs r) = foldMap (foldMap f) r

instance
  (Traversable r, Traversable m) => Traversable (Abs r m)
  where
    traverse f (Abs r) = Abs <$> traverse (traverse f) r
-}
instance (Functor r, Functor f) => Bound (Abs p r) where
  Block r m     >>>= f = Block (fmap (>>= f) <$> r) (m >>= f)
  Closure p a b >>>= f = Closure p (a >>>= f) (b >>>= f)


type VarName a b c = 
  Either (Public a) (Either (Local b) c)
  

fromBindings
 :: MonadExpr (Abs Assoc Multi) m
 => Bindings
      Int
      (Declared These Assoc)
      (Pattern (Multi (Declared These Assoc)))
      (m (Var Name Ident Ident a))
 -> Abs
      (Defined Assoc)
      (Scope (Public ()) m)
      (Var Name b Ident a)
fromBindings (In fa) = fromDeclared fa
fromBinding (Let p a sba) =
  Closure p (lift a) b
  where
    b = fromBindings (Scope . return . either (B . local) F <$> b')

fromPattern
 :: Declared These Assoc ()
 -> b
 -> Abs (Defined Assoc) m b
fromPattern 


fromDeclared
 :: MonadExpr (Abs Assoc Components) m
 => Declared These Assoc (NonEmpty (m (VarName Ident Ident a)))
 -> m (VarName p Ident a)
 -> Abs Assoc Components (Scope (Public ()) m) (VarName p Ident a)
fromDeclared (Declared r k) b = Abs lm
  where
    lcls =
      Closure
        (lp $> pure ())
        (wrapExpr (Abs (Block (lift <$> lp)))) pcls
    pcls =
      Closure (pp $> pure ()) (lift (lift (lift b))) (Block pp)
  
    pp =
      mapWithIndex
        (\ i f -> f (Local i))
        (Pattern
          (toComponent (abstractPublic . k) <$>
            publicComponents r)
          (pure . Scope . return . B))
      where
        toComponent
         :: (a -> [b])
         -> (Public a, Maybe (Local a))
         -> Components b
        toComponent f (Public a, Nothing) = publicList (f a)
        toComponent f (Public a, Just (Local b)) =
          Public (f a) :? Local (f b)
          
        publicList xs = Public xs :? Local []
        
        abstractPublic b c =
          Scope <$>
            fromListPaths
              (\ b _ ->
                unscope . lift . abstractVarName ns 
                  <$> toList b)
              b
              (B c)
        
        fromListPaths
         :: (Traversable r, MonadExpr r Components m)
         => (b -> a -> [m a])
         -> Paths r b -> a -> [m a]
        fromListPaths f (Leaf b) a = f b a
        fromListPaths f (Node r k) a = pure (fromListNode f r k a)
        fromListPaths f (Overlap r k b) a =
          pure (fromListNode f r k a) <|> f b a
          where
            fromListNode f r k =
              fromNode (\ b a -> publicList <$> f b a) r k
    
    
    (ns, lp) =
      sequenceA
        (Pattern
          (fmap 
            (\ (n, a) -> ([Just (Local n)], toPath n a))
            (localComponents r))
          ([Nothing], Leaf empty))
      where
        toPath n Nothing = pure (return (Left n))
        toPath n (Just x) =
          fromPaths
            (\ b _ ->
              abstractVarName ns <$> publicList (toList b))
            b
            (Right (Left (Local n)))


data Components f a = Public (f a) :? Local (f a)
  deriving (Functor, Foldable, Traversable)

instance Applicative f => Applicative (Components f) where
  pure a = Public (pure a)
  Public ff :? Local fg <*> Public fa :? Local fb =
    Public (ff <*> fa) :? Local (fg <*> fb)

instance Alternative f => Alternative (Components f) where
  empty = empty :? empty
  Public fa :? Local ga <|> Public fb :? Local gb =
    Public (fa <|> fb) :? Local (ga <|> gb)


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
        Right (Left (Local n)) -> case elemIndex n ns of
          Just i -> F (return (B (Local i)))
          Nothing -> F (return (Right (Left (Local n))))
        Right (Right x) ->
          F (return (F (return (Right (Right x)))))))

newtype Super a = Super { getSuper :: a }

data Versions f m a =
    Null
  | Current (f (m a)) (Versions f m a)
  | m a :# Verions f (Scope (Super ()) m) a
  deriving (Functor, Foldable, Traversable)

instance Functor f => Bound (Versions f) where
  Null          >>>= f = Null
  Current fm vs >>>= f = Current (fmap (>>= f) fm) (p >>>= f)
  m :# vs       >>>= f = (m >>= f) :# (vs >>>= f)  


fromPaths
 :: (Alternative f, Traversable r, MonadExpr (Abs r f) m)
 => (b -> a -> f (m a))
 -> Paths r b -> a -> f (m a)
fromPaths f = fromPaths' f where
  fromPaths' f (Leaf b) a = f b a
  fromPaths' f (Node r k) a = pure (fromNode f r k a)
  fromPaths' f (Overlap r k b) a = pure (fromNode f k r a) <|> f b a
    
fromNode
 :: (Alternative f, Traversable r, MonadExpr (Abs r f) m)
 => (b -> a -> f (m a))
 -> r x
 -> (x -> Paths r b)
 -> a -> m a
fromNode f r k a = wrapExpr (Abs cls) where
  pm =
    mapWithIndex
      (\ i f -> f (Local i))
      (Pattern
        (abstractPaths f . k <$> r)
        (pure . Scope . return . B))
  
  cls =
    Closure (pm $> pure ()) (return a) (Block pm)
    
abstractPaths 
 :: (Alternative f, Traversable r, MonadExpr (Abs r f) m)
 => (b -> a -> f (m a))
 -> Paths r b -> c -> f (Scope c m a)
abstractPaths f a c =
  Scope <$> fromPaths (\ b a -> unscope . lift <$> f b a) (B c) a

      
mapWithIndex
 :: Traversable t
 => (Int -> a -> b) -> t a -> t b
mapWithIndex f t =
  snd (mapAccumL (\ i a -> (i+1, f i a)) 0 t)

{-
data MaybeWith a b =
    Alone a
  | With a b
  deriving (Functor, Foldable, Traversable)
  
instance Bifunctor MaybeWith where bimap = bimapDefault

instance Bifoldable MaybeWith where bifoldMap = bifoldMapDefault

instance Bitraversable MaybeWith where
  bitraverse f g (as :? bs) =
    (:?) <$> traverse f as <*> traverse g bs
-}

publicComponents
 :: Control These Assoc a
 -> Assoc (Public a, Maybe (Local a))
publicComponents (Control r) = mapMaybe maybeThis r
  where
    maybeThis
     :: These a b -> Maybe (a, Maybe b)
    maybeThis (This a) = Just (a, Nothing)
    maybeThis (That _) = Nothing
    maybeThis (These a b) = Just (a, Just b)

localComponents
 :: Control These Assoc a
 -> Assoc (Ident, Maybe a)
localComponents (Control r) = mapWithKey referenceHere r
  where
    referenceHere
     :: Ident
     -> These (Public a) (Local b)
     -> (Ident, Maybe a)
    referenceHere n (This (Public _)) = (n, Nothing)
    referenceHere n (These (Public _) _) = (n, Nothing)
    referenceHere n (That (Local b)) = (n, Just b)


-- | Marker type for self- and env- references
newtype Extern a = Extern { getExtern :: a }



-- | Wrap nested expressions
class Monad m => MonadExpr r m | m -> r where
  wrapExpr :: Expr r m a -> m a

instance MonadExpr (Abs Assoc f) (Repr f) where
  wrapExpr f = join (Repr f)

instance
  MonadExpr (Abs r f) m => MonadExpr (Abs r f) (Scope b m)
  where
    wrapExpr f = Scope (wrapExpr (hoistExpr hoistAbs unScope f))

{-

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