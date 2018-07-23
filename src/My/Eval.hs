{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, Open )
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
eval :: (Ord k, Show k) => Open (Tag k) a -> Open (Tag k) a
eval (Prim p)         = Prim (evalPrim p)
eval (Let en x)       = f x where
    f = eval . instantiate (en' !!)
    en' = map f en
eval (c `At` x)       = evalAt (closed c) x
eval (c `AtPrim` t)   = closed c `AtPrim` t
eval (o1 `Update` o2) = eval o1 `Update` eval o2
eval o                = o
  
  
closed
  :: (Ord k, Show k)
  => Closed (Tag k) (Open (Tag k) a) -> Closed (Tag k) (Open (Tag k) a)
closed (a1 `App` a2)    = evalApp (eval a1) (eval a2)
closed (c `Fix` x)      = closed c `Fix` x
closed (c1 `Concat` c2) = closed c1 `Concat` closed c2
closed c                = c
  
  
evalApp
  :: (Ord k, Show k)
  => Open (Tag k) a -> Open (Tag k) a -> Closed (Tag k) (Open (Tag k) a)
evalApp o se = go Nothing o where
  go m (Prim (Number d))  = errorWithoutStackTrace "self: number #unimplemented"
  go m (Prim (Text s))    = errorWithoutStackTrace "self: text #unimplemented"
  go m (Prim (Bool b))    = goDefn m (boolDefn b)
  go m (Prim (IOError e)) = errorWithoutStackTrace "self: ioerror #unimplemented"
  go m (Defn d)           = goDefn m d
  go m (o1 `Update` o2)   = su `Concat` go (Just su) o2 where
    su = go m o1
  go m o                  = maybe id Concat m (o `App` se)
  
  goDefn m d = closed (instantiate (binding se su) <$> d) where
    su = maybe emptyBlock (Defn . fmap lift) m
    
  emptyBlock = Defn (Block M.empty)
  
  
evalAt
  :: (Ord k, Show k)
  => Closed (Tag k) (Open (Tag k) a) -> Tag k -> Open (Tag k) a
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
  => Prim (Open (Tag k) a) -> Prim (Open (Tag k) a)
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
    
    prim :: (Prim (Open k a) -> Maybe b) -> Open k a -> Maybe b
    prim k a = go a where
      go (Prim p)         = k p
      go (c1 `Update` c2) = go c2 <|> go c1
      go a                = Nothing
      
    bool :: Prim (Open k a) -> Maybe Bool
    bool a = case a of
      Bool b -> Just b
      Unop Not _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Lt, Gt, Eq, Ne, Le, Ge, And, Or]
          then Nothing else boole
      _ -> boole
      
    num :: Prim (Open k a) -> Maybe Double
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
boolDefn :: Bool -> Closed (Tag k) (Scope Binding (Open (Tag k)) a)
boolDefn b = (Block . M.singleton (Key "match") . Scope)
  (self (Var (B Self)) `At` if b then Key "ifTrue" else Key "ifFalse")

  