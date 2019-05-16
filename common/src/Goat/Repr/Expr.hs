{-# LANGUAGE ExistentialQuantification, FlexibleContexts, GeneralizedNewtypeDeriving, DeriveTraversable, StandaloneDeriving, MultiParamTypeClasses, RankNTypes, LambdaCase #-}

-- | This module contains core data type representing parsed code.
-- This is a pure data representation suitable for optimisation,
-- validation and interpretation.
-- The core data type implements the typeclass encoding of the Goat syntax from 'Goat.Lang.Class'.
module Goat.Repr.Expr where

-- import Goat.Repr.Assoc
import Goat.Repr.Pattern
import Goat.Util (abstractEither, (<&>))
import Control.Applicative (Alternative(..), Const(..))
import Control.Monad (ap, liftM, join)
import Control.Monad.Trans (MonadTrans(..))
import Data.Bifunctor
import Data.Functor (($>))
import Data.These (these, These(..))
import Data.List (elemIndex)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map as Map
import Data.String (IsString(..))
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
  | Sel (m a) Text
  | Add (m a) (m a)
  | Sub (m a) (m a)
  | Mul (m a) (m a)
  | Div (m a) (m a)
  | Pow (m a) (m a)
  | Eq (m a) (m a)
  | Ne (m a) (m a)
  | Lt (m a) (m a)
  | Le (m a) (m a)
  | Gt (m a) (m a)
  | Ge (m a) (m a)
  | Or (m a) (m a)
  | And (m a) (m a)
  | Not (m a)
  | Neg (m a)

hoistExpr
 :: (Functor r, Functor m)
 => (forall x . m x -> n x) -> Expr r m a -> Expr r n a
hoistExpr f = \case
  Number d -> Number d
  Text t   -> Text t
  Bool b   -> Bool b
  Block r  -> Block (hoistAbs f r)
  Null     -> Null
  Sel a k  -> Sel (f a) k
  Add a b  -> Add (f a) (f b)
  Sub a b  -> Sub (f a) (f b)
  Mul a b  -> Mul (f a) (f b)
  Div a b  -> Div (f a) (f b)
  Pow a b  -> Pow (f a) (f b)
  Eq  a b  -> Eq  (f a) (f b)
  Ne  a b  -> Ne  (f a) (f b)
  Lt  a b  -> Lt  (f a) (f b)
  Le  a b  -> Le  (f a) (f b)
  Gt  a b  -> Gt  (f a) (f b)
  Ge  a b  -> Ge  (f a) (f b)
  Or  a b  -> Or  (f a) (f b)
  And a b  -> And (f a) (f b)
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
    traverse f = \case
      Number d -> pure (Number d)
      Text t   -> pure (Text t)
      Bool b   -> pure (Bool b)
      Block r  -> Block <$> traverse f r
      Null     -> pure Null
      Sel a k  -> traverse f a <&> (`Sel` k)
      Add a b  -> op Add a b
      Sub a b  -> op Sub a b
      Mul a b  -> op Mul a b
      Div a b  -> op Div a b
      Pow a b  -> op Pow a b
      Eq  a b  -> op Eq  a b
      Ne  a b  -> op Ne  a b
      Gt  a b  -> op Gt  a b
      Ge  a b  -> op Ge  a b
      Lt  a b  -> op Lt  a b
      Le  a b  -> op Le  a b
      Or  a b  -> op Or  a b
      And a b  -> op And a b
      Not a    -> Not <$> traverse f a
      Neg a    -> Neg <$> traverse f a
      where
        op g a b = g <$> traverse f a <*> traverse f b

instance Functor r => Bound (Expr r) where
  Number d >>>= _ = Number d
  Text t   >>>= _ = Text t
  Bool b   >>>= _ = Bool b
  Block r  >>>= f = Block (r >>>= f)
  Null     >>>= _ = Null
  Sel a k  >>>= f = Sel (a >>= f) k
  Add a b  >>>= f = Add (a >>= f) (b >>= f)
  Sub a b  >>>= f = Sub (a >>= f) (b >>= f)
  Mul a b  >>>= f = Mul (a >>= f) (b >>= f)
  Div a b  >>>= f = Div (a >>= f) (b >>= f)
  Pow a b  >>>= f = Pow (a >>= f) (b >>= f)
  Eq  a b  >>>= f = Eq  (a >>= f) (b >>= f)
  Ne  a b  >>>= f = Ne  (a >>= f) (b >>= f)
  Gt  a b  >>>= f = Gt  (a >>= f) (b >>= f)
  Ge  a b  >>>= f = Ge  (a >>= f) (b >>= f)
  Lt  a b  >>>= f = Lt  (a >>= f) (b >>= f)
  Le  a b  >>>= f = Le  (a >>= f) (b >>= f)
  Or  a b  >>>= f = Or  (a >>= f) (b >>= f)
  And a b  >>>= f = And (a >>= f) (b >>= f)
  Not a    >>>= f = Not (a >>= f)
  Neg a    >>>= f = Neg (a >>= f)
--

-- type Ident = Text
type VarName a b c = 
  Either (Public a) (Either (Local b) c)

reprFromBindings
 :: MonadBlock (Abs Components) m
 => Bindings Declares (Components ()) m (VarName Ident Ident a)
 -> m (VarName b Ident a)
 -> m (VarName b Ident a)
reprFromBindings bs m = wrapBlock abs
  where
    -- bs scopes outer to inner: super, env
    ((Local lp, Public pp), bs') =
      squashBindings <$>
        transverseBindings
          componentsBlockFromDeclares
          (hoistBindings (lift . lift) bs)
    
    (ns, penv) = captureComponents lp
    
     -- abstract local variables before binding outer scope values
    bsAbs = abstractVarName ns . return <$> bs'
    bsSuper = letParts pp (lift (lift m)) bsAbs
    bsEnv = letParts lp (lift (lift penv)) bsSuper
    
     -- bind local variables
    abs =
      Abs (Let lp (hoistBindings (lift . lift) bsEnv >>>= id))
    
    
    captureComponents
     :: MonadBlock (Abs Components) m
     => Components a
     -> ([Maybe Ident], m (VarName b Ident c))
    captureComponents (Inside (Extend r _)) =
      wrapBlock . Abs . Define . Inside <$>
        sequenceA
          (Extend
            (Map.mapWithKey
              (\ n _ -> ([Just n], [lname n]))
              r)
            ([Nothing], []))
      where
        lname = return . Right . Left . Local


componentsBlockFromDeclares
 :: MonadBlock (Abs Components) m
 => Declares a
 -> ( (Local (Components ()), Public (Components ()))
    , Bindings
       (Parts Identity Components)
       (Components ())
       (Scope (Local Int) (Scope (Local Int) m))
       a
    )
componentsBlockFromDeclares (Declares (Local lr) (Public pr) k) =
  ( (Local lp, Public pp)
  , liftBindings2 Parts 
      (hoistBindings lift lbs')
      (hoistBindings (hoistScope lift) pbs)
  )
  where
    (pp, pbs) =
      componentsBlockFromNode (reprFromAssigns . k <$> pr)
    (lp, lbs) =
      componentsBlockFromNode (reprFromAssigns . k <$> lr)
    lbs' =
      embedBindings (hoistBindings lift . wrapLocal) lbs
     
    wrapLocal
     :: (Functor r, Applicative h, MonadBlock (Abs r) m)
     => r a -> Bindings h p m a
    wrapLocal r =
      Define (pure (wrapBlock (Abs (Define (return <$> r)))))
    
    reprFromAssigns
     :: MonadBlock (Abs Components) m
     => Assigns (Map Text) (NonEmpty a)
     -> Int -> [Scope (Local Int) m a]
    reprFromAssigns m =
      reprFromAssignsWith
        reprFromNode
        (reprFromLeaf <$> m)

reprFromLeaf
 :: (Foldable t, Monad m) => t a -> b -> [m a]
reprFromLeaf t _ = Monoid.getAlt (foldMap (pure . return) t)

reprFromNode
 :: MonadBlock (Abs Components) m
 => Components ()
 -> Block Components (Scope (Local Int) m) a
 -> Int -> [Scope (Local Int) m a]
reprFromNode p bs i = [Scope (wrapBlock abs)] where
  abs =
    Abs
      (hoistBindings lift
        (letParts p (B (Local i)) (F . return <$> bs)))
{-
punComponentsFromDeclares
 :: ( Foldable t
    , MonadBlock (Abs (Pattern (Option (Privacy These)))) m
    )
 => Declares a
 -> ( Components ()
    , Block
        Components
        (Scope (Local Int) (Scope (Local Int) m))
        b
    )
punComponentsFromDeclares (Declares (Local r) (Public r) k) =
  componentsFromNode
    (blockAssignsWith punNode . fmap punLeaf . k <$> r)

-- | 'punLeaf p v i' returns a value obtained from the inner scoped parent
punLeaf
 :: (Monad m, Applicative g)
 => a -> Int -> g (Scope b (Scope (Local Int) m) c)
punLeaf _ i = pure (lift (Scope (return (B (Local i)))))

-- | 'punComponents p v i' generates a value which binds two versions of 'i'
punComponents
 :: MonadBlock (Abs Components) m
 => Components ()
 -> Block Components (Scope (Local Int) (Scope (Local Int) m)) b
 -> Int
 -> [Scope (Local Int) (Scope (Local Int) m) b]
punComponents pg m i =
  [Scope (Scope (wrapBlock (Abs (hoistBindings lift mouter))))]
  where
    m' = inner (outer (F . return . F . return <$> m))
    -- bind outer scope of 'm' to fields of outer scope
    outer = Let pg (return (F (return (B (Local i)))))
    -- bind inner scope of 'm' to fields of inner scope
    inner = Let pg (return (B (Local i)))
-}

-- | 'reprFromAssignsWith kp asgs i' generates a value from set of assigns 'asgs'.
-- Values for intermediate nodes are generated by using 'kp' to merge the pattern and corresponding value with fields generated by the node's children.
reprFromAssignsWith
 :: Monad m
 => (Components () ->
      Block Components (Scope (Local Int) m) a ->
      Int ->
      [Scope (Local Int) m a])
 -> Assigns (Map Text) (Int -> [Scope (Local Int) m a])
 -> Int -> [Scope (Local Int) m a]
reprFromAssignsWith kp =
  merge .
    iterAssigns
      (\ r ->
        case componentsBlockFromNode (merge <$> r) of
          (p, m) -> kp p m)
  where
    merge = these id id mappend

-- | 'bindingParts r k' generates a pattern matching the fields of 'Assoc' 'r' and a corresponding binding value with identical fields with values generated by the fields of 'r'.
componentsBlockFromNode
 :: Monad m
 => Map Text (Int -> [Scope (Local Int) m a])
 -> ( Components ()
    , Bindings Components p (Scope (Local Int) m) a
    )
componentsBlockFromNode r = (p, bs)
  where
    x = Extend r (pure . Scope . return . B . Local)
    p = Inside (x $> pure ())
    xm = mapWithIndex (\ i f -> f i) x
    bs = Define (Inside xm)
    

-- | abstract bound identifiers, with inner and outer levels of local bindings
abstractVarName
 :: (Monad m, Eq a)
 => [Maybe a]
 -> m (VarName p a b)
 -> Scope (Local Int) (Scope (Public p) m) (VarName q a b)
abstractVarName ns m =
  Right <$> abstractLocal ns (abstractPublic m)
  where
    abstractPublic = abstractEither id
    abstractLocal ns =
      abstract (\case
        Left (Local n) -> Local <$> elemIndex (Just n) ns
        Right _ -> Nothing)


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