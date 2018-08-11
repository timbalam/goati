{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, Repr )
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
eval (Val c e)      = Val (cached c) (eval e)
eval (Prim p)       = Prim (evalPrim p)
eval (Let en x)     = f x where
    f = eval . instantiate (en' !!)
    en' = map f en
eval (c `At` x)     = evalAt (cached c) x
eval (c `AtPrim` t) = cached c `AtPrim` t
eval (e `Update` w) = evalUpdate (eval e) (eval w)
eval e              = e

evalUpdate :: (Ord k, Show k) => Repr (Tag k) a -> Repr (Tag k) a -> Repr (Tag k) a
evalUpdate e (Val _ d) = v where
  v = Val (evalApp se v) e'
  se = instantiate1 e d

  e' = wrap (unwrap d >>= \ v -> case v of
    B () -> pure (B ()) `Sconcat` lift e
    F e  -> lift e)
    
  wrap = Super . Scope 
  unwrap = unScope . unSuper
evalUpdate e w                 = e `Update` w
    



cached
  :: (Ord k, Show k)
  => Cached (Tag k) (Repr (Tag k) a)
  -> Cached (Tag k) (Repr (Tag k) a)
cached (Cached e)       = case eval e of
  Val c _ -> c
  e       -> Cached e
cached (e1 `App` e2)    = evalApp (eval e1) (eval e2)
cached (c `Fix` x)      = cached c `Fix` x
cached (c1 `Concat` c2) = cached c1 `Concat` cached c2
cached c                = c

evalApp
  :: (Ord k, Show k)
  => Repr (Tag k) a -> Repr (Tag k) a -> Cached (Tag k) (Repr (Tag k) a)
evalApp (Val _ e) v      = cached c' where
  c' = Cached (instantiate (ref em v) e)
  em = Val (Block M.empty) (lift em)
evalApp (e `Update` w) v = cached (e `App` v) `Concat` cached (w `App` v)
evalApp e              v = e `App` v
  
  
goPrim m (Number d)  = errorWithoutStackTrace "eval: number #unimplemented"
goPrim m (Text s)    = errorWithoutStackTrace "eval: text #unimplemented"
goPrim m (Bool b)    = goDefn m (boolDefn b)
goPrim m (IOError e) = errorWithoutStackTrace "eval: ioerror #unimplemented"
  
  
evalAt
  :: (Ord k, Show k)
  => Cached (Tag k) (Repr (Tag k)) a -> Tag k -> Repr (Tag k) a
evalAt c k =  fromMaybe evale (go c) where
  evale = error ("eval: not a component: " ++ show k)
  
  go (Block b)         = eval <$> M.lookup k b
  go (c `Fix` x)
    | k == x           = Nothing
    | otherwise        = go c
  go (c1 `Concat` c2)  = go c2 <|> go c1
  go c                 = Just (c `At` k)


evalPrim
  :: (Ord k, Show k)
  => Prim (Repr (Tag k) a) -> Prim (Repr (Tag k) a)
evalPrim p = case p of
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
    
    bool2bool f op e = maybe (Unop op e) (Bool . f) (prim bool e)
    num2num f op e = maybe (Unop op e) (Number . f) (prim num e)
    num2num2num f op a b = maybe (Binop op a b) Number (liftA2 f (prim num a) (prim num b))
    num2num2bool f op a b = maybe (Binop op a b) Bool (liftA2 f (prim num a) (prim num b))
    bool2bool2bool f op a b = maybe (Binop op a b) Bool (liftA2 f (prim bool a) (prim bool b))
    
    prim :: (Prim (Repr k a) -> Maybe b) -> Repr k a -> Maybe b
    prim k a = go a where
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

        
-- | Bool
boolDefn :: Ord k => Bool -> Cached (Tag k) (Scope Ref (Repr (Tag k))) a
boolDefn b = (Block . M.singleton (Key "match") . Scope)
  ((Cached . Var) (B Self) `At` if b then Key "ifTrue" else Key "ifFalse")

  