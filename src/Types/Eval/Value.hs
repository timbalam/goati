{-# LANGUAGE FlexibleContexts #-}
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
  
import Types.Parser
import qualified Types.Error as E
import Types.Eval.Ided
import Types.Eval.Cell
import Types.Util

import Control.Monad.Catch( throwM, MonadThrow )
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.IO.Class
import Control.Exception
import qualified Data.Map as M
import Data.IORef
import Data.Typeable


-- Env / Self
type Cell = IORef (IO Value)
type Env = M.Map FieldId Cell
type Self = Env
type IOW = WriterT (EndoM IO ()) IO
type Node = Configurable IOW Self Self


emptyEnv :: Env
emptyEnv = M.empty


emptyNode :: Node
emptyNode = mempty


-- Value
data Value =
    String String
  | Number Double
  | Bool Bool
  | Node (IORef (Maybe Self)) Node


instance Show Value where
  show (String x) =
    show x
  
  show (Number x) =
    show x
    
  show (Bool x)   =
    show x
  
  show (Node _ _) =
    "<Node>"


instance Eq Value where
  String x == String x' =
    x == x'
  
  Number x == Number x' =
    x == x'
  
  Bool x == Bool x' =
    x == x'
  
  Node x _ == Node x' _ =
    x == x'
  
  _ == _ =
    False
  
  
newNode :: MonadIO m => m (Node -> Value)
newNode =
  Node <$> liftIO (newIORef Nothing)
    
    
unNode :: Value -> Node
unNode =
  go
    where
      go (Number x) =
        selfToNode (primitiveNumberSelf x)
        
      go (String x) =
        selfToNode (primitiveStringSelf x)
      
      go (Bool x) =
        selfToNode (primitiveBoolSelf x)
  
      go (Node _ c) =
        c
      
      
      selfToNode :: IO Self -> Node
      selfToNode m =
        EndoM (\ self0 ->
          M.union <$> liftIO m <*> pure self0)

    
-- Primitives
primitiveStringSelf :: MonadIO m => String -> m Self
primitiveStringSelf x =
  return emptyEnv


primitiveNumberSelf :: MonadIO m => Double -> m Self
primitiveNumberSelf x =
  return emptyEnv


primitiveBoolSelf :: MonadIO m => Bool -> m Self
primitiveBoolSelf x =
  return emptyEnv


primitiveNumberUnop :: MonadThrow m => Unop -> Double -> m Value
primitiveNumberUnop Neg x =
  (return . Number . negate) x
  
primitiveNumberUnop s       _ =
  E.throwUndefinedNumberOp s


primitiveBoolUnop :: MonadThrow m => Unop -> Bool -> m Value
primitiveBoolUnop Not x =
  (return . Bool . not) x

primitiveBoolUnop s       _ =
  E.throwUndefinedBoolOp s


primitiveNumberBinop :: MonadThrow m => Binop -> Double -> Double -> m Value
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
  E.throwUndefinedNumberOp s


primitiveBoolBinop :: MonadThrow m => Binop -> Bool -> Bool -> m Value
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
  E.throwUndefinedBoolOp s


inputNode :: MonadIO m => m Value
inputNode =
  Node
    <$> liftIO (newIORef Nothing)
    <*> pure
      (EndoM (\ self ->
         M.insert (Field "getLine")
           <$> newCell (liftIO getLine >>= return . String)
           <*> pure self))

         
primitiveBindings :: MonadIO m => m Env
primitiveBindings = 
  M.insert (Field "input")
    <$> newCell inputNode
    <*> pure emptyEnv
    
