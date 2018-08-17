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
eval e = e' where
  e' = evalWith (fromMaybe emptyBlock) e' e
  emptyBlock = Block M.empty M.empty


evalWith
  :: (Ord k, Show k)
  => (Maybe (Repr (Tag k) a) -> Repr (Tag k) a)
  -> Repr (Tag k) a
  -> Repr (Tag k) a
  -> Repr (Tag k) a
evalWith su se x = go x where
  go (Let en s)     = go (f s) where
    f = instantiate (en' !!)
    en' = map (eval . f) en
  go (Block _ b)      = Block (M.map f b) b where
    f = eval . instantiate (ref (f Nothing) se)
  go (Prim p)       = Prim (prim p)
  go (Call x e1 e2) = callWith x (evalWith (fromMaybe emptyBlock) e2' e1) e2' (evalWith su se) where
    e2' = eval e2
    emptyBlock = Block M.empty M.empty
  go (e1 `Update` e2) = e1' `Update` evalWith su' se e2 where
    e1' = go e1
    su' = su . Just . maybe e1' (e1 `Update`)
  go (e `Fix` k)    = e' where
    e' = evalWith su e' e
  go x              = x
    

callWith
  :: (Ord k, Show k)
  => Tag k -> Repr (Tag k) a -> Repr (Tag k) a
  -> (Repr (Tag k) a -> Repr (Tag k) a)
  -> Repr (Tag k) a
callWith k e se f = fromMaybe evale (go id e) where
  evale = error ("eval: not a component: " ++ show k)
  
  go f (Block b)        = f . fst <$> M.lookup k b
  go f (e `Fix` x)
    | k == x            = Nothing
    | otherwise         = go f e
  go f (e1 `Update` e2) = go (f . f') e2 <|> go f e1 where
    f' = (e1 `Update`)
  go f e                = Just (Call k (f e) se)
  
  
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
boolDefn :: Ord k => Bool -> Repr (Tag k) a
boolDefn b = d where
  d = Block (M.singleton (Key "match") (e, se))
  se = Scope (pure (B Self) S.#. if b then "ifTrue" else "ifFalse")
  e = eval (instantiate (ref emptyBlock d) se)
  emptyBlock = Block M.empty M.empty
  
  


  