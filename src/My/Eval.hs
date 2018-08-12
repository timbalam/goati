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
eval (Val d e)      = Val (defn d) (eval e)
eval (Let en x)     = f x where
    f = eval . instantiate (en' !!)
    en' = map f en
eval (Prim p)       = Prim (prim p)
eval (d `At` x)     = fromMaybe evale (go (defn d)) where
  evale = error ("eval: not a component: " ++ show k)
  
  go (Block b)         = eval <$> M.lookup k b
  go (d `Fix` x)
    | k == x           = Nothing
    | otherwise        = go d
  go (d1 `Concat` d2)  = go d2 <|> go d1
  go d                 = Just (d `At` k)
eval (d `AtPrim` t) = defn d `AtPrim` t
eval (e `Update` w) = case eval w of 
  Val _ se -> eval (instantiate1 e' se)
  w'       -> e' `Update` w'
  where
    e' = eval e
eval e              = e


defn :: (Ord k, Show k) => Defn (Tag k) a -> Defn (Tag k) a
defn (Defn e)       = go (eval e) where
  go (Val d _)        = d
  go e'               = Defn e'
defn (d `App` e)    = go (defn d) where
  go (Block b)        = Block (M.Map (app e') b)
  go (d1 `Concat` d2) = go d1 `Concat` go d2
  go d'               = d' `App` e'
  
  e' = eval e
  app e (_, se) = (e', lift e') where
    e' = eval (instantiate1 e se)
defn (d `Fix` x)      = defn d `Fix` x
defn (d1 `Concat` d2) = defn d1 `Concat` defn d2
defn d                = d
  
  
goPrim m (Number d)  = errorWithoutStackTrace "eval: number #unimplemented"
goPrim m (Text s)    = errorWithoutStackTrace "eval: text #unimplemented"
goPrim m (Bool b)    = goDefn m (boolDefn b)
goPrim m (IOError e) = errorWithoutStackTrace "eval: ioerror #unimplemented"
  

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

        
-- | Bool
boolDefn :: Ord k => Bool -> Defn (Tag k) a
boolDefn b = d where
  d = Block (M.singleton (Key "match") (e, se))
  se = (Scope . Defn . Var) (B Self) `At` if b then Key "ifTrue" else Key "ifFalse"
  e = instantiate (valDefn d) se
  
  


  