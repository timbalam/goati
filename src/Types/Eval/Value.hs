{-# LANGUAGE FlexibleContexts, OverloadedStrings, DeriveFunctor #-}
module Types.Eval.Value
  ( Env
  , Self
  , Node
  , Cell
  , IOW
  , emptyEnv
  , emptyNode
  , newNode
  , unNode
  , Value(..)
  , primitiveNumberUnop
  , primitiveNumberBinop
  , primitiveNumberSelf
  , primitiveBoolUnop
  , primitiveBoolBinop
  , primitiveBoolSelf
  , primitiveStringSelf
  , primitiveBindings
  )
  where
  

import Types.Parser( Binop(..), Unop(..), ShowMy(..) )
import qualified Types.Error as E
import Types.Eval.Ided
import Types.Eval.Cell
import Types.Util.Configurable

import qualified Data.Text as T
import qualified Data.Map as M
import Control.Applicative (liftA2)
import Bound


-- Interpreted my-language expression
data Expr a =
    String T.Text
  | Number Double
  | Bool Bool
  | Var a
  | Block (M.Map Tag (Scope Tag Expr a)) [Expr a]
  | Expr a `At` Tag
  | Expr a `Del` Tag
  | Expr a `Update` Expr a
  deriving (Eq, Functor, Foldable, Traversable)
  
  
instance Monad Expr where
  return = Var
  
  
  String s >>= f =
    String s
    
  Number d >>= f =
    Number d
    
  Bool b >>= f =
    Bool b
    
  Var a >>= f =
    f a
    
  Block m e >>= f =
    Block (map (>>>= f) xs) (e >>= f)
    
  e `At` x >>= f =
    (e >>= f) `At` x
    
  e `Del` x >>= f =
    (e >>= f) `Del` x
    
  e1 `Update` e2 >>= f
    (e1 >>= f) `Update` (e2 >>= f)
  
  
instance ShowMy a => ShowMy (Expr a) where
  showMy (String x) =
    show x
  
  showMy (Number x) =
    show x
    
  showMy (Bool x)   =
    show x
    
  showMy (Var a) =
    showMy a
    
  showMy (Block m) =
    "<Node>"
    
  showMy (e `At` x) =
    showMy e ++ "." ++ showMy x
    
  showMy (e `Del` x) =
    showMy e ++ "~" ++ showMy x
    
  showMy (e1 `Update` e2) =
    showMy e1 ++ "(" ++ showMy e2 ++ ")"
    
    
    
-- Match expression tree
data M a = V a | Tr (M.Map Tag (M a))

emptyM = Tr M.empty


mergeM :: M a -> M a -> Maybe (M a)
mergeM (Tr m) (Tr n)  = Tr <$> unionAWith mergeM m n
mergeM _      _       = Nothing


instance Monoid (Maybe (M a)) where
  mempty = Just emptyM
  
  
  mappend = join . liftA2 mergeM


-- Set expression tree
data S a = S (M.Map a (M (Expr a)))

emptyS = S M.empty


mergeS :: S a -> S a -> Maybe (S a)    
mergeS (S a) (S b) =
  S <$> unionAWith mergeM a b
  
  
instance Monoid (Maybe (S a)) where
  mempty = Just emptyS
  
  mappend = join . liftA2 mergeS
  


pathS :: Free Field a -> Expr a -> S a
pathS path = tree path . V


punS :: Free Field a -> S a
punS path = tree path emptyS


tree :: Free Field a -> a -> S a
  where
    go (Pure a) =
      S . M.singleton a
      
    go (Free (path `At` x)) =
      go path . Tr . M.singleton x

  
pathM :: Free Field Tag -> a -> M a
pathM path = go path . V
  where
    go (Pure x) =
      Tr . M.singleton x

    go (Free (path `At` x)) =
      go path . Tr . M.singleton x
      

blockM :: M (Expr a -> Maybe (S a)) -> Expr a -> Maybe (S a)
blockM = go
  where
    go :: (Expr a -> Expr a) -> M (Expr a -> Maybe (S a)) -> Expr a -> Maybe (S a)
    go (V f) e = f e
    
    go (Tr m) e =
      M.foldMapWithKey (flip go . Proj e)
  

blockS :: S (Vis Tag) -> [Expr (Vis Tag)] -> Expr (Vis Tag)
blockS (S m) es =
  Block self es
  where
    (self, env) =
      partition (map go m)
      
    
    substPriv :: Vis Tag -> Expr (Vis Tag)
    substPriv =
      vis
        (return . Pub)
        (maybe (return . Priv) id . flip M.lookup env)
    
    
    go :: M (Expr (Vis Tag)) -> Scope Tag Expr (Vis Tag)
    go (V e) = abstract maybePub (e >>= substPriv)
    go (Tr m) =
      do
        m' <- traverseWithKey (goUnder . Var . Pub) m
        return (Block m' [])
        
    goUnder :: Expr (Vis Tag) -> M (Expr (Vis Tag)) -> Scope Tag (Scope Tag Expr) Vis Tag
    goUnder _ a@(V _) = hoistScope lift (go a)
    goUnder e (Tr m) =
      do
        m' <- traverseWithKey (goUnder . At e) m
        return (Block m' [foldr Del e (M.keys m)])
    
    
    partition :: M.Map (Vis a) b -> (M.Map a b, M.Map a b)
    partition =
      foldrWithKey
        (\ k a (s, e) ->
          case k of
            Priv x -> (s, M.insert x a e)
            Pub x -> (M.insert x a s, e))
        (M.empty, M.empty)
        
  
  
unionAWith :: (a -> b -> f c) -> M.Map k a -> M.Map k b -> f (M.Map k c)
unionAWith f =
  M.mergeA
    M.preserveMissing
    M.preserveMissing
    M.zipWithAMatched (\ _ -> f)
      
      
 

    
-- Primitives
runValue :: Value a -> Self a
runValue =
  go
    where
      go (Number x) =
        primitiveNumberSelf x
        
      go (String x) =
        primitiveStringSelf x
      
      go (Bool x) =
        primitiveBoolSelf x
  
      go (Node s) =
        s
primitiveStringSelf :: T.Text -> Self a
primitiveStringSelf x =
  emptySelf


primitiveNumberSelf :: Double -> Self a
primitiveNumberSelf x =
  emptySelf


primitiveBoolSelf :: Bool -> Self a
primitiveBoolSelf x =
  emptySelf


primitiveNumberUnop :: Unop -> Double -> Maybe Value
primitiveNumberUnop Neg x =
  (return . Number . negate) x
  
primitiveNumberUnop s       _ =
  Nothing


primitiveBoolUnop :: Unop -> Bool -> Maybe Value
primitiveBoolUnop Not x =
  (return . Bool . not) x

primitiveBoolUnop s       _ =
  Nothing


primitiveNumberBinop :: Binop -> Double -> Double -> Maybe Value
primitiveNumberBinop Add x y =
  return . Number $ x + y

primitiveNumberBinop Sub x y =
  return . Number $ x - y

primitiveNumberBinop Prod x y =
  return . Number $ x * y

primitiveNumberBinop Div x y =
  return . Number $ x / y

primitiveNumberBinop Pow x y =
  return . Number $ x ** y

primitiveNumberBinop Lt x y =
  return . Bool $ x < y

primitiveNumberBinop Gt x y =
  return . Bool $ x > y

primitiveNumberBinop Eq x y =
  return . Bool $ x == y

primitiveNumberBinop Ne x y =
  return . Bool $ x /= y

primitiveNumberBinop Le x y =
  return . Bool $ x <= y

primitiveNumberBinop Ge x y =
  return . Bool $ x >= y

primitiveNumberBinop s _ _ =
  Nothing


primitiveBoolBinop :: Binop -> Bool -> Bool -> Maybe Value
primitiveBoolBinop And x y =
  return . Bool $ x && y

primitiveBoolBinop Or x y =
  return . Bool $ x || y

primitiveBoolBinop Lt x y =
  return . Bool $ x < y

primitiveBoolBinop Gt x y =
  return . Bool $ x > y

primitiveBoolBinop Eq x y =
  return . Bool $ x == y

primitiveBoolBinop Ne x y =
  return . Bool $ x /= y

primitiveBoolBinop Le x y =
  return . Bool $ x <= y

primitiveBoolBinop Ge x y =
  return . Bool $ x >= y

primitiveBoolBinop s _ _ =
  Nothing


         
primitiveBindings :: Env a
primitiveBindings =
  emptyEnv
    
