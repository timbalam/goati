{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
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


-- Env / Self
type Member a = ReaderT (Self a) Maybe (Endo (Maybe (Value a)))

    
newtype Self a = Self { getSelf :: M.Map a (Member a) }


lookup :: a -> Self a -> Maybe (Member a)
lookup a (Self m) = M.lookup a m


insert :: a -> Member a -> Self a -> Self a
insert a r (Self m) = Self (M.insert a r m)

alter :: (Maybe (Member a) -> Maybe (Member a)) -> a -> Self a -> Self a
alter f a (Self m) = Self (M.alter f a m)


type Env a = Self a


emptyEnv = Self M.empty


emptySelf = Self M.empty


-- Value
data Value a =
    String T.Text
  | Number Double
  | Bool Bool
  | Node (Self a)


instance ShowMy (Value a) where
  showMy (String x) =
    show x
  
  showMy (Number x) =
    show x
    
  showMy (Bool x)   =
    show x
  
  showMy (Node _) =
    "<Node>"
  
    
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

    
-- Primitives
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
    
