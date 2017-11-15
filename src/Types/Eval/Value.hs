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
  | OpenB (M.Map Tag (Expr a))
  | ClosedB (M.Map Tag (Scope Tag Expr a))
  | Match (Expr a) Pat (Scope Int Expr a)
  deriving (Eq, Functor, Foldable, Traversable)
  
  
data Pat =
    OpenP (M.Map Tag Pat)
  | WildP (M.Map Tag Pat)
  
  
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
    
  OpenB m >>= f =
    OpenB (map (>>= f) m)
    
  ClosedB m >>= f =
    ClosedB (map (>>>= f) xs)
    
  Match e p b >>= f =
    Match (e >>= f) p (b >>>= f)

  
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
    
  showMy (Match e p b) =
    "let " ++ showMy p ++ "=" ++ showMy e
    
    
showsPatWithTokens :: Show a => (a -> a) -> a -> Pat -> String -> String
showsPatWithTokens next start p s = snd (go p (start, s))
  where
    go (Open m) (a, s) =
      (next a', "{ " ++ s' ++ " ... " ++ show a' ++ " }" ++ s)
      where
        (a', s') = internal m a
        
    go (Wild m) (a, s) =
      (a', "{ " ++ s' ++ " ... }" ++ s)
      where 
        (a', s') = internal m (a, "")
  
  
    internal m a =
      foldrWithKey
        (\ k p (a, s) ->
          let
            (a', s') = go p (a, s)
          in 
            (a', " " ++ showsMy k (" = " ++ s')))
        (a, "")
        m
  
    
instance ShowMy Pat where
    ShowsMy =
      showsPatWithTokens (+1) 1
    
    
    
-- Pattern constructors
data M a = V a | Tr (M.Map Tag (M a))

emptyM = Tr M.empty


mergeM :: M a -> M a -> Maybe (M a)
mergeM (Tr m) (Tr n)  = Tr <$> unionAWith mergeM m n
mergeM _      _       = Nothing


data S a = S (M.Map a (M (Expr a)))

emptyS = S M.empty


mergeS :: S a -> S a -> Maybe (S a)    
mergeS (S a) (S b) =
  S <$> unionAWith mergeM a b


pathS :: Free Field a -> Expr a -> S a
pathS path = go path . V
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
      
      
consM :: [Maybe (M a)] -> Maybe (M a)
consM = 
  foldr
    (\ ma mb -> do { a <- ma; b <- mb; mergeM a b })
    (Just emptyM)
      

blockM :: M (Expr a -> Maybe (S a)) -> Expr a -> Maybe (S a)
blockM = go id
  where
    go :: ((Int, Pat) -> (Int, Pat)) -> T a -> Expr a -> Maybe (S a)
    go p (V f) e = (f . Match e pat . Scope . Var . B) i
      where
        (i, pat) = p (1, OpenP M.empty)
    
    go p (Tr m) e =
      M.foldrWithKey
        (\ k t mb -> do { a <- go (p . delp k) t e; b <- mb, mergeS a b })
        Just emptyS
        m
      where
        delp k (i, pat) = ((,) i . WildP . M.singleton k) pat
      
      
consS :: [Maybe (S a)] -> Maybe (S a)
consS =
  foldr
    (\ ma mb -> do { a <- ma; b <- mb; mergeS a b })
    (Just emptyS)
      
  

blockS :: S (Vis Tag) -> Expr (Vis Tag)
blockS (S m) =
  (ClosedB . map (abstract abstPub)) self
  where
    (self, env) =
      (partition . map ((>>= substPriv (flip M.lookup env) . toExpr)) m
    
    
    toExpr :: M (Expr (Vis Tag)) -> Expr (Vis Tag)
    toExpr (V e) = e
    toExpr (Tr m) = OpenB (map toExpr m)
    
    
    abstPub :: Vis Tag -> Maybe Tag
    abstPub (Pub x) = Just x
    abstPub (Priv _) = Nothing
    
    
    substPriv :: (Vis Tag -> Maybe (Expr (Vis Tag))) -> Vis Tag -> Expr (Vis Tag)
    substPriv f a@(Pub _)  = return a
    substPriv f a@(Priv x) = maybe (return a) id (f x))
    
    
    partition :: M.Map (Vis a) b -> (M.Map a b, M.Map a b)
    partition =
      foldrWithKey
        (\ k a (s, e) ->
          case k of
            Priv x -> (s, M.insert x a e)
            Pub x -> (M.insert x a s, e))
        (M.empty, M.empty)
        
        
updateS :: Expr (Vis Tag) -> S (Vis Tag) -> S (Vis Tag)
updateS e (S m) =
  S (mapWithKey go m)
  where
    go (Pub x) (Tr m) =
      V 
        (Match
          e 
          ((OpenP . M.singleton x . OpenP) M.empty)
          (Scope . ClosedB . (toExpr m)))
    go _ a = a
    
    
    updateTag :: Tag -> Expr a -> M (Expr a) -> Expr a
  
  
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
    
