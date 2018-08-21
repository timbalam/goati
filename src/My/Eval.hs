{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval )
where

import My.Types.Repr
import My.Types.Error
import My.Types.Interpreter
import My.Types.Syntax.Class
import My.Util ((<&>), Susp(..))
import Data.List.NonEmpty (NonEmpty)
import Data.Bifunctor
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Void
import Control.Applicative (liftA2, (<|>))
import Control.Monad (join, (<=<), ap)
import Control.Monad.Trans
import Control.Monad.Free (Free(..))
import Control.Exception (IOException, catch)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Functor.Identity (Identity(..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import System.IO (Handle, IOMode, withFile)
import Bound (Scope(..), instantiate)

  
-- | Reduce an expression as much as possible, halting for irreducible expressions
-- e.g. involving unsolved free variables.
eval :: (Ord k, Show k) => Repr (Tag k) a -> Repr (Tag k) a
eval e = maybe e eval (evalStep e)


evalStep
  :: (Ord k, Show k) => Repr (Tag k) a -> Maybe (Repr (Tag k) a)
evalStep (Let en s)       = Just (f s) where
  f = instantiate (en' !!)
  en' = map (eval . f) en
evalStep (Prim p)         = Prim <$> prim p
evalStep (c `At` x)       = callStep x c
evalStep e                = Nothing
  

callStep
  :: (Ord k, Show k)
  => k -> Closed k IdentityT (Repr k) a -> Maybe (Repr k a)
callStep x c = fromMaybe evale . go emptyBlock where
  evale = error ("eval: not a component: " ++ show k)
  
  go (Block b)        = Just <$> M.lookup k b
  go (c `Fix` x')
    | x' == x         = Nothing
    | otherwise       = go c
  go (c1 `Concat` c2) = go c2 <|> fmap (<|> (c1 `At` x)) (go c1)
  go su _             = Just Nothing
  
  emptyBlock = Block M.empty
  

val :: Open (Tag k) (Repr (Tag k)) a -> Repr (Tag k) a
val o = e where
  e = Val (closed c) o
  c = emptyVal `Update` (o `App` e)
  emptyVal = Val (Block M.empty) (Self (Super (Block M.empty)))

  
closed :: Closed k IdentityT (Repr k) a -> Closed k IdentityT (Repr k) a
closed = go where
  f = IdentityT . eval . runIdentityT
  
  go (Closed e) = case f e of
    IdentityT (Val c _) -> c
    e                   -> Closed e
  go (Block b) = Block (M.map f b)
  go (c `Fix` x) = go c `Fix` x
  go (e `Update` d) = case defns d of
    Super c -> go (super e c)
    d       -> e `Update` d
  go (c1 `Concat` c2) = go c1 `Concat` go c2
  
  
defns (o `App` e) = case open o of
  Self d -> defns (self (eval e) d)
  o      -> o `App` e
defns d           = d


open :: (Ord k, Show k) => Open (Tag k) (Repr (Tag k)) a -> Open (Tag k) (Repr (Tag k)) a
open (Open e) = case eval e of
  Val _ o -> open o
  e       -> Open e
open e        = e


self
  :: (Ord k, Show k)
  => Repr (Tag k) a
  -> Defns (Tag k) (Scope ()) (Repr (Tag k)) a
  -> Defns (Tag k) IdentityT (Repr (Tag k)) a
self e = self' where
  f = IdentityT . instantiate e
  f' = T_ . f . getT_ 
  
  self' (Super d) = Super (go d)
  self' (o `App` s) = o `App` f s
  
  go (Closed e) = Closed (f' e)
  go (Block b) = Block (M.map f' b)
  go (c `Fix` x) = go c `Fix` x
  go (e `Update` d) = f' e `Update` d
  go (c1 `Concat` c2) = go c1 `Concat` go c2

super
  :: (Ord k, Show k)
  => Repr (Tag k) a
  -> Closed (Tag k) (T IdentityT (Scope ())) (Repr (Tag k)) a 
  -> Closed (Tag k) IdentityT (Repr (Tag k)) a
super e = go where
  f = IdentityT . instantiate e . runIdentity . getT_

  go (Closed e)       = Closed (f e)
  go (Block b)        = Block (M.map f b)
  go (c `Fix` x)      = go c `Fix` x
  go (e `Update` d)   = f e `Update` d
  go (c1 `Concat` c2) = go c1 `Concat` go c2
  
  
  

prim
  :: (Ord k, Show k) => Prim (Repr (Tag k) a) -> Prim (Repr (Tag k) a)
prim p = case p of
  -- constants
  Number d        -> Number d
  Text s          -> Text s
  Bool b          -> Bool b
  IOError e       -> IOError e
  
  -- operations
  Unop op a       -> unop op op (eval a)
  Binop op a b    -> binop op op (eval a) (eval b)
  where
    unop Not = bool2bool not
    unop Neg = num2num negate
    
    binop Add  = num2num2num (+)
    binop Sub  = num2num2num (-)
    binop Prod = num2num2num (*)
    binop Div  = num2num2num (/)
    binop Pow  = num2num2num (**)
    binop Gt   = num2num2bool (>) 
    binop Lt   = num2num2bool (<)
    binop Eq   = num2num2bool (==)
    binop Ne   = num2num2bool (/=)
    binop Ge   = num2num2bool (>=)
    binop Le   = num2num2bool (<=)
    binop Or   = bool2bool2bool (||)
    binop And  = bool2bool2bool (&&)
    
    bool2bool f op e = maybe (Unop op e) (Bool . f) (withprim bool e)
    num2num f op e = maybe (Unop op e) (Number . f) (withprim num e)
    num2num2num f op a b = maybe (Binop op a b) Number
      (liftA2 f (withprim num a) (withprim num b))
    num2num2bool f op a b = maybe (Binop op a b) Bool
      (liftA2 f (withprim num a) (withprim num b))
    bool2bool2bool f op a b = maybe (Binop op a b) Bool
      (liftA2 f (withprim bool a) (withprim bool b))
    
    withprim :: (Prim (Repr k a) -> Maybe b) -> Repr k a -> Maybe b
    withprim k a = go a where
      go (Prim p)         = k p
      go a                = Nothing
      
    bool :: Prim (Repr k a) -> Maybe Bool
    bool a = case a of
      Bool b -> Just b
      Unop Not _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Lt, Gt, Eq, Ne, Le, Ge, And, Or]
          then Nothing else boole
      _ -> boole
      
    num :: Prim (Repr k a) -> Maybe Double
    num a = case a of
      Number d -> Just d
      Unop Neg _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Add, Sub, Div, Prod, Pow]
          then Nothing else nume
      _ -> nume
    
    nume = errorWithoutStackTrace "eval: number type"
    boole = errorWithoutStackTrace "eval: bool type"

  
  
  


  