{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, DeriveFunctor #-}

-- | Evaluators for my language expressions
module My.Eval
  ( eval, simplify, Comp, Susp(..), Free(..)
  , K, Open, toDefns, instantiateDefns, instantiateSelf
  )
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
import Control.Applicative (liftA2)
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
eval :: Open (Tag k) a -> Open (Tag k) a
eval (Prim p)         = Prim (evalPrim p)
eval (Let en x)       = f x where
    f = (eval . instantiate) (en' !!)
    en' = map (eval . f) en
eval (c `At` x)       = evalAt (closed c) x
eval (c `AtPrim` t)   = closed c `AtPrim` t
eval (o1 `Update` o2) = eval o1 `Update` eval o2
eval o                = o
  
  
closed :: Closed (Tag k) (Open (Tag k) a) -> Closed (Tag k) (Open (Tag k) a)
closed (a1 `App` a2)    = evalApp (eval a1) (eval a2)
closed (c `Fix` x)      = closed c `Fix` x
closed (c1 `Concat` c2) = closed c1 `Concat` closed c2
closed c                = c
  
  
evalApp :: Open (Tag k) a -> Open (Tag k) a -> Closed (Tag k) (Open (Tag k) a)
evalApp o se = go Nothing o where
  emptyBlock = Defns (Block M.empty)
  
  go m (Defn d)         = closed (instantiate (binding se su) <$> d) where
    su = fromMaybe emptyBlock m
  go m (o1 `Update` o2) = su `Concat` go (Just su) o2 where
    su = go m o1
  go m o                = maybe id Update m o `App` se
  
  
evalAt :: Closed (Tag k) (Open (Tag k) a) -> Tag k -> Open (Tag k) a
evalAt c k =  fromMaybe evale (go c) where
  evale = error ("eval: not a component: " ++ show k)
  
  go (Prim p `App` se) = evalPrimAt p se k
  go (Block b)         = eval <$> M.lookup k b
  go (c `Fix` x)
    | k == x           = Nothing
    | otherwise        = go c
  go (c1 `Concat` c2)  = go c2 <|> go c1
  go c                 = Just (c `At` k)
      
  
      

-- | Self forms for primitives
evalPrimAt :: Prim (Closed (Tag k) a) -> Open (Tag k) a -> Tag k -> Open (Tag k) a
evalPrimAt (Number d)  se k = errorWithoutStackTrace "self: number #unimplemented"
evalPrimAt (Text s)    se k = errorWithoutStackTrace "self: text #unimplemented"
evalPrimAt (Bool b)    se k = evalBoolAt b se k
evalPrimAt (IOError e) se k = errorWithoutStackTrace "self: ioerror #unimplemented"
evalPrimAt p           se k = (Prim p `App` se) `At` k


evalPrim :: Prim (Closed (Tag k) (Open (Tag k) a)) -> Prim (Closed (Tag k) (Open (Tag k) a))
evalPrim p = fromMaybe p (case p of
  -- constants
  Number d        -> Nothing
  Text s          -> Text s
  Bool b          -> Bool b
  IOError e       -> IOError e
  
  -- pure operations
  Unop op a       -> unop op op (closed a)
  Binop op a b    -> binop op op (closed a) (closed b))
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
    
    prim a k = go a where
      go (Prim p `App` _) = k p
      go (Block _)        = Nothing
      go (c `Fix` _)      = go c
      go (c1 `Concat` c2) = go c2 <|> go c1
      go a                = Just a
      
    
    bool a = case a of
      Bool b -> Just b
      Unop Not _ -> Nothing
      Binop op _ _ ->
        if op `elem` [Lt, Gt, Eq, Ne, Le, Ge, And, Or]
          then Nothing else boole
      _ -> boole
      
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
evalBoolAt :: Bool -> Open (Tag k) a -> Tag k -> Maybe (Open (Tag k) a)
evalBoolAt b se k = case k of
  Key "match" -> if b then Just (se #. "ifTrue") else Just (se #. "ifFalse")
  _           -> Nothing

  